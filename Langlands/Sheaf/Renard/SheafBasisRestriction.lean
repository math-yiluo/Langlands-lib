import Langlands.Sheaf.Renard.BasisRestriction

/-!
# Restriction of all-open sheaves and comparison of germ constructions

Separation follows from actual all-open gluing uniqueness. Chosen-basis
compatibility is promoted to all-open compatibility by basis refinement.
-/

open CategoryTheory Opposite TopologicalSpace

universe u v w

namespace Langlands.Sheaf.Renard

variable {X : Type u} [TopologicalSpace X]

/-- Genuine all-open gluing uniqueness separates sections on every covering family. -/
theorem allOpen_family_separated (G : BasisSheaf.{u,v} (allOpenBasis X))
    {ι : Type w} (V : BasisOpen (allOpenBasis X))
    (U : ι → BasisOpen (allOpenBasis X)) (hU : FamilyCovers V U)
    (s t : Sections G.obj.obj V)
    (hst : ∀ i, restriction G.obj.obj (hU.1 i) s =
      restriction G.obj.obj (hU.1 i) t) : s = t := by
  have hs : Compatible G.obj.obj U (fun i => restriction G.obj.obj (hU.1 i) s) := by
    intro i j W hWi hWj
    rw [restriction_comp_apply, restriction_comp_apply]
  obtain ⟨a, _, ha⟩ := G.unique_gluing V U hU
    (fun i => restriction G.obj.obj (hU.1 i) s) hs
  exact (ha s (fun _ => rfl)).trans (ha t (fun i => (hst i).symm)).symm

/-- Every actual open is covered by all chosen-basis opens contained in it. -/
theorem basisRefinement_covers (B : OpenBasis X) (W : BasisOpen (allOpenBasis X)) :
    FamilyCovers W
      (fun T : {T : BasisOpen B // T.obj ≤ W.obj} => allOpen T.val.obj) := by
  refine ⟨fun T => T.property, ?_⟩
  intro x hx
  obtain ⟨T, hxT, hTW⟩ := B.exists_subset W.obj hx
  exact ⟨⟨T, hTW⟩, hxT⟩

/-- An all-open sheaf's sections are determined by restrictions to the chosen basis. -/
theorem allOpen_sections_eq_of_basis_restrictions (B : OpenBasis X)
    (G : BasisSheaf.{u,v} (allOpenBasis X)) (W : BasisOpen (allOpenBasis X))
    (s t : Sections G.obj.obj W)
    (hst : ∀ (T : BasisOpen B) (hT : T.obj ≤ W.obj),
      restriction G.obj.obj (U := allOpen T.obj) hT s =
        restriction G.obj.obj (U := allOpen T.obj) hT t) : s = t :=
  allOpen_family_separated G W
    (fun T : {T : BasisOpen B // T.obj ≤ W.obj} => allOpen T.val.obj)
    (basisRefinement_covers B W) s t (fun T => hst T.val T.property)

/-- Basis compatibility promotes to compatibility on every actual open overlap. -/
theorem basisCompatible_allOpenCompatible (B : OpenBasis X)
    (G : BasisSheaf.{u,v} (allOpenBasis X)) {ι : Type w}
    (U : ι → BasisOpen B)
    (s : ∀ i, Sections ((rawBasisRestriction B).obj G.obj.obj) (U i))
    (hs : Compatible ((rawBasisRestriction B).obj G.obj.obj) U s) :
    Compatible G.obj.obj (fun i => allOpen (U i).obj) s := by
  intro i j W hWi hWj
  apply allOpen_sections_eq_of_basis_restrictions B G W
  intro T hT
  calc
    restriction G.obj.obj (U := allOpen T.obj) hT
        (restriction G.obj.obj hWi (s i)) =
        restriction G.obj.obj (U := allOpen T.obj) (hT.trans hWi) (s i) :=
      restriction_comp_apply G.obj.obj hT hWi (s i)
    _ = restriction G.obj.obj (U := allOpen T.obj) (hT.trans hWj) (s j) :=
      hs i j T (hT.trans hWi) (hT.trans hWj)
    _ = restriction G.obj.obj (U := allOpen T.obj) hT
        (restriction G.obj.obj hWj (s j)) :=
      (restriction_comp_apply G.obj.obj hT hWj (s j)).symm

/-- Intrinsic restricted gluing for covers in every independent index universe. -/
theorem rawBasisRestriction_familySheafCondition (B : OpenBasis X)
    (G : BasisSheaf.{u,v} (allOpenBasis X)) :
    FamilySheafCondition.{u,v,w} ((rawBasisRestriction B).obj G.obj.obj) := by
  intro ι V U hU s hs
  have hU' : FamilyCovers (allOpen V.obj) (fun i => allOpen (U i).obj) := hU
  exact G.unique_gluing (allOpen V.obj) (fun i => allOpen (U i).obj) hU' s
    (basisCompatible_allOpenCompatible B G U s hs)

/-- Restriction satisfies precisely the existing literal set-cover sheaf predicate. -/
theorem rawBasisRestriction_sheafCondition (B : OpenBasis X)
    (G : BasisSheaf.{u,v} (allOpenBasis X)) :
    SheafCondition ((rawBasisRestriction B).obj G.obj.obj) :=
  FamilySheafCondition.sheafCondition _ (rawBasisRestriction_familySheafCondition B G)

/-- Restrict actual all-open sheaves to the chosen basis, preserving the value universe. -/
def sheafBasisRestriction (B : OpenBasis X) :
    BasisSheaf.{u,v} (allOpenBasis X) ⥤ BasisSheaf.{u,v} B where
  obj G := ⟨(basisRestriction B).obj G.obj, rawBasisRestriction_sheafCondition B G⟩
  map φ := ObjectProperty.homMk ((basisRestriction B).map φ.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
theorem sheafBasisRestriction_obj_presheaf (B : OpenBasis X)
    (G : BasisSheaf.{u,v} (allOpenBasis X)) :
    ((sheafBasisRestriction B).obj G).obj = (basisRestriction B).obj G.obj := rfl

@[simp]
theorem sheafBasisRestriction_obj_raw (B : OpenBasis X)
    (G : BasisSheaf.{u,v} (allOpenBasis X)) :
    ((sheafBasisRestriction B).obj G).obj.obj =
      (rawBasisRestriction B).obj G.obj.obj := rfl

@[simp]
theorem sheafBasisRestriction_sections (B : OpenBasis X)
    (G : BasisSheaf.{u,v} (allOpenBasis X)) (U : BasisOpen B) :
    Sections ((sheafBasisRestriction B).obj G).obj.obj U =
      Sections G.obj.obj (allOpen U.obj) := rfl

@[simp]
theorem sheafBasisRestriction_restriction (B : OpenBasis X)
    (G : BasisSheaf.{u,v} (allOpenBasis X)) {U V : BasisOpen B} (h : U.obj ≤ V.obj) :
    restriction ((sheafBasisRestriction B).obj G).obj.obj h =
      restriction G.obj.obj (U := allOpen U.obj) (V := allOpen V.obj) h := rfl

@[simp]
theorem sheafBasisRestriction_map_app (B : OpenBasis X)
    {F G : BasisSheaf.{u,v} (allOpenBasis X)} (φ : F ⟶ G) (U : BasisOpen B) :
    ((sheafBasisRestriction B).map φ).hom.hom.app (op U) =
      φ.hom.hom.app (op (allOpen U.obj)) := rfl

/-- The normalized forgetful comparison is a literal functor equality. -/
theorem sheafBasisRestriction_comp_forget (B : OpenBasis X) :
    sheafBasisRestriction.{u,v} B ⋙ sheafForget B =
      sheafForget (allOpenBasis X) ⋙ basisRestriction B := rfl

/-- The raw forgetful comparison is also literal. -/
theorem sheafBasisRestriction_comp_raw (B : OpenBasis X) :
    sheafBasisRestriction.{u,v} B ⋙ sheafForget B ⋙ presheafInclusion B =
      sheafForget (allOpenBasis X) ⋙ presheafInclusion (allOpenBasis X) ⋙
        rawBasisRestriction B := rfl

/-- Extension and restriction retain exactly the chosen-basis germ functor. -/
theorem rawAllOpenGerm_restrict_eq (B : OpenBasis X) :
    rawAllOpenGermSheafFunctor.{u,v} B ⋙ sheafBasisRestriction B =
      rawGermSheafFunctor B := rfl

/-- The normalized specialization retains exactly the same germ functor. -/
theorem allOpenGerm_restrict_eq (B : OpenBasis X) :
    allOpenGermSheafFunctor.{u,v} B ⋙ sheafBasisRestriction B =
      germSheafFunctor B := rfl

/-- The canonical comparison is identity on the existing germ-section carriers. -/
noncomputable def rawAllOpenGermRestrictionIso (B : OpenBasis X) :
    rawAllOpenGermSheafFunctor.{u,v} B ⋙ sheafBasisRestriction B ≅
      rawGermSheafFunctor B :=
  Iso.refl _

/-- The normalized comparison is the same identity on actual germ families. -/
noncomputable def allOpenGermRestrictionIso (B : OpenBasis X) :
    allOpenGermSheafFunctor.{u,v} B ⋙ sheafBasisRestriction B ≅
      germSheafFunctor B :=
  Iso.refl _

@[simp]
theorem rawAllOpenGermRestriction_sections (B : OpenBasis X)
    (F : RawPresheaf.{u,v} B) (U : BasisOpen B) :
    Sections (((rawAllOpenGermSheafFunctor B ⋙ sheafBasisRestriction B).obj F).obj.obj) U =
      AddCommGrpCat.of (GermSections F U.obj) := rfl

@[simp]
theorem rawAllOpenGermRestriction_restriction (B : OpenBasis X)
    (F : RawPresheaf.{u,v} B) {U V : BasisOpen B} (h : U.obj ≤ V.obj) :
    (restriction ((rawAllOpenGermSheafFunctor B ⋙ sheafBasisRestriction B).obj F).obj.obj
      h).hom = germRestriction F h := rfl

@[simp]
theorem rawAllOpenGermRestriction_map_app (B : OpenBasis X)
    {F G : RawPresheaf.{u,v} B} (φ : F ⟶ G) (U : BasisOpen B) :
    (((rawAllOpenGermSheafFunctor B ⋙ sheafBasisRestriction B).map φ).hom.hom.app
      (op U)).hom = germSectionsMap φ U.obj := rfl

@[simp]
theorem rawAllOpenGermRestrictionIso_hom_app (B : OpenBasis X)
    (F : RawPresheaf.{u,v} B) (U : BasisOpen B) :
    ((rawAllOpenGermRestrictionIso B).hom.app F).hom.hom.app (op U) =
      𝟙 (AddCommGrpCat.of (GermSections F U.obj)) := rfl

@[simp]
theorem rawAllOpenGermRestrictionIso_inv_app (B : OpenBasis X)
    (F : RawPresheaf.{u,v} B) (U : BasisOpen B) :
    ((rawAllOpenGermRestrictionIso B).inv.app F).hom.hom.app (op U) =
      𝟙 (AddCommGrpCat.of (GermSections F U.obj)) := rfl

@[simp]
theorem rawAllOpenGermRestrictionIso_hom_apply (B : OpenBasis X)
    (F : RawPresheaf.{u,v} B) (U : BasisOpen B) (s : GermSections F U.obj) :
    (((rawAllOpenGermRestrictionIso B).hom.app F).hom.hom.app (op U)) s = s := rfl

@[simp]
theorem rawAllOpenGermRestrictionIso_inv_apply (B : OpenBasis X)
    (F : RawPresheaf.{u,v} B) (U : BasisOpen B) (s : GermSections F U.obj) :
    (((rawAllOpenGermRestrictionIso B).inv.app F).hom.hom.app (op U)) s = s := rfl

/-- The hom comparison commutes with the original germ restriction itself. -/
theorem rawAllOpenGermRestrictionIso_hom_restriction (B : OpenBasis X)
    (F : RawPresheaf.{u,v} B) {U V : BasisOpen B} (h : U.obj ≤ V.obj)
    (s : GermSections F V.obj) :
    (((rawAllOpenGermRestrictionIso B).hom.app F).hom.hom.app (op U))
        (germRestriction F h s) =
      germRestriction F h
        ((((rawAllOpenGermRestrictionIso B).hom.app F).hom.hom.app (op V)) s) := rfl

/-- The inverse comparison commutes with the original germ restriction itself. -/
theorem rawAllOpenGermRestrictionIso_inv_restriction (B : OpenBasis X)
    (F : RawPresheaf.{u,v} B) {U V : BasisOpen B} (h : U.obj ≤ V.obj)
    (s : GermSections F V.obj) :
    (((rawAllOpenGermRestrictionIso B).inv.app F).hom.hom.app (op U))
        (germRestriction F h s) =
      germRestriction F h
        ((((rawAllOpenGermRestrictionIso B).inv.app F).hom.hom.app (op V)) s) := rfl

/-- Naturality acts on the actual germSectionsMap, for arbitrary raw inputs. -/
theorem rawAllOpenGermRestrictionIso_hom_naturality (B : OpenBasis X)
    {F G : RawPresheaf.{u,v} B} (φ : F ⟶ G) (U : BasisOpen B)
    (s : GermSections F U.obj) :
    (((rawAllOpenGermRestrictionIso B).hom.app G).hom.hom.app (op U))
        (germSectionsMap φ U.obj s) =
      germSectionsMap φ U.obj
        ((((rawAllOpenGermRestrictionIso B).hom.app F).hom.hom.app (op U)) s) := rfl

theorem rawAllOpenGermRestrictionIso_inv_naturality (B : OpenBasis X)
    {F G : RawPresheaf.{u,v} B} (φ : F ⟶ G) (U : BasisOpen B)
    (s : GermSections F U.obj) :
    (((rawAllOpenGermRestrictionIso B).inv.app G).hom.hom.app (op U))
        (germSectionsMap φ U.obj s) =
      germSectionsMap φ U.obj
        ((((rawAllOpenGermRestrictionIso B).inv.app F).hom.hom.app (op U)) s) := rfl

@[simp]
theorem allOpenGermRestriction_sections (B : OpenBasis X)
    (F : Presheaf.{u,v} B) (U : BasisOpen B) :
    Sections ((allOpenGermSheafFunctor B ⋙ sheafBasisRestriction B).obj F).obj.obj U =
      AddCommGrpCat.of (GermSections F.obj U.obj) := rfl

@[simp]
theorem allOpenGermRestriction_restriction (B : OpenBasis X)
    (F : Presheaf.{u,v} B) {U V : BasisOpen B} (h : U.obj ≤ V.obj) :
    (restriction ((allOpenGermSheafFunctor B ⋙ sheafBasisRestriction B).obj F).obj.obj
      h).hom = germRestriction F.obj h := rfl

@[simp]
theorem allOpenGermRestriction_map_app (B : OpenBasis X)
    {F G : Presheaf.{u,v} B} (φ : F ⟶ G) (U : BasisOpen B) :
    (((allOpenGermSheafFunctor B ⋙ sheafBasisRestriction B).map φ).hom.hom.app
      (op U)).hom = germSectionsMap φ.hom U.obj := rfl

@[simp]
theorem allOpenGermRestrictionIso_hom_app (B : OpenBasis X)
    (F : Presheaf.{u,v} B) (U : BasisOpen B) :
    ((allOpenGermRestrictionIso B).hom.app F).hom.hom.app (op U) =
      𝟙 (AddCommGrpCat.of (GermSections F.obj U.obj)) := rfl

@[simp]
theorem allOpenGermRestrictionIso_inv_app (B : OpenBasis X)
    (F : Presheaf.{u,v} B) (U : BasisOpen B) :
    ((allOpenGermRestrictionIso B).inv.app F).hom.hom.app (op U) =
      𝟙 (AddCommGrpCat.of (GermSections F.obj U.obj)) := rfl

@[simp]
theorem allOpenGermRestrictionIso_hom_apply (B : OpenBasis X)
    (F : Presheaf.{u,v} B) (U : BasisOpen B) (s : GermSections F.obj U.obj) :
    (((allOpenGermRestrictionIso B).hom.app F).hom.hom.app (op U)) s = s := rfl

@[simp]
theorem allOpenGermRestrictionIso_inv_apply (B : OpenBasis X)
    (F : Presheaf.{u,v} B) (U : BasisOpen B) (s : GermSections F.obj U.obj) :
    (((allOpenGermRestrictionIso B).inv.app F).hom.hom.app (op U)) s = s := rfl

theorem allOpenGermRestrictionIso_hom_restriction (B : OpenBasis X)
    (F : Presheaf.{u,v} B) {U V : BasisOpen B} (h : U.obj ≤ V.obj)
    (s : GermSections F.obj V.obj) :
    (((allOpenGermRestrictionIso B).hom.app F).hom.hom.app (op U))
        (germRestriction F.obj h s) =
      germRestriction F.obj h
        ((((allOpenGermRestrictionIso B).hom.app F).hom.hom.app (op V)) s) := rfl

theorem allOpenGermRestrictionIso_inv_restriction (B : OpenBasis X)
    (F : Presheaf.{u,v} B) {U V : BasisOpen B} (h : U.obj ≤ V.obj)
    (s : GermSections F.obj V.obj) :
    (((allOpenGermRestrictionIso B).inv.app F).hom.hom.app (op U))
        (germRestriction F.obj h s) =
      germRestriction F.obj h
        ((((allOpenGermRestrictionIso B).inv.app F).hom.hom.app (op V)) s) := rfl

theorem allOpenGermRestrictionIso_hom_naturality (B : OpenBasis X)
    {F G : Presheaf.{u,v} B} (φ : F ⟶ G) (U : BasisOpen B)
    (s : GermSections F.obj U.obj) :
    (((allOpenGermRestrictionIso B).hom.app G).hom.hom.app (op U))
        (germSectionsMap φ.hom U.obj s) =
      germSectionsMap φ.hom U.obj
        ((((allOpenGermRestrictionIso B).hom.app F).hom.hom.app (op U)) s) := rfl

theorem allOpenGermRestrictionIso_inv_naturality (B : OpenBasis X)
    {F G : Presheaf.{u,v} B} (φ : F ⟶ G) (U : BasisOpen B)
    (s : GermSections F.obj U.obj) :
    (((allOpenGermRestrictionIso B).inv.app G).hom.hom.app (op U))
        (germSectionsMap φ.hom U.obj s) =
      germSectionsMap φ.hom U.obj
        ((((allOpenGermRestrictionIso B).inv.app F).hom.hom.app (op U)) s) := rfl

end Langlands.Sheaf.Renard
