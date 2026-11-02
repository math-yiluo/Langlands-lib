import Langlands.Sheaf.Renard.GermSections
import Langlands.Sheaf.Renard.BasisSheaf

/-!
# Direct gluing of locally represented germ sections

An auxiliary target basis packages the same families on either the original
basis or all actual opens. The original stalks always come from the input basis.
-/

open CategoryTheory Opposite TopologicalSpace

universe u v w

namespace Langlands.Sheaf.Renard

variable {X : Type u} [TopologicalSpace X] {B : OpenBasis X}

/-- The same actual germ families and restrictions, evaluated on any target basis. -/
noncomputable def germPresheafOn (C : OpenBasis X) (F : RawPresheaf.{u,v} B) :
    RawPresheaf.{u,max u v} C where
  obj U := AddCommGrpCat.of (GermSections F U.unop.obj)
  map f := AddCommGrpCat.ofHom (germRestriction F f.unop.hom.le)
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
theorem germPresheafOn_obj (C : OpenBasis X) (F : RawPresheaf.{u,v} B)
    (U : BasisOpen C) :
    Sections (germPresheafOn C F) U = AddCommGrpCat.of (GermSections F U.obj) := rfl

@[simp]
theorem germPresheafOn_restriction (C : OpenBasis X) (F : RawPresheaf.{u,v} B)
    {U V : BasisOpen C} (h : U.obj ≤ V.obj) :
    (restriction (germPresheafOn C F) h).hom = germRestriction F h := rfl

theorem germPresheafOn_isNormalized (C : OpenBasis X) (F : RawPresheaf.{u,v} B) :
    IsNormalized (germPresheafOn C F) := by
  intro U hU
  change Subsingleton (GermSections F U.obj)
  rw [hU]
  infer_instance

/-- Literal compatibility implies equality of values, by refining the overlap at that point. -/
theorem compatible_germSections_value (C : OpenBasis X) (F : RawPresheaf.{u,v} B)
    {ι : Type w} (U : ι → BasisOpen C) (s : ∀ i, Sections (germPresheafOn C F) (U i))
    (hs : Compatible (germPresheafOn C F) U s) (i j : ι)
    (x : X) (hxi : x ∈ (U i).obj) (hxj : x ∈ (U j).obj) :
    (s i).val ⟨x, hxi⟩ = (s j).val ⟨x, hxj⟩ := by
  obtain ⟨W, hxW, hW⟩ := C.exists_subset ((U i).obj ⊓ (U j).obj) ⟨hxi, hxj⟩
  exact congrArg (fun z : GermSections F W.obj => z.val ⟨x, hxW⟩)
    (hs i j W (hW.trans inf_le_left) (hW.trans inf_le_right))

/-- Choose a member containing each point; no choice is needed at points of an empty domain. -/
noncomputable def germGlueFamily (C : OpenBasis X) (F : RawPresheaf.{u,v} B)
    {ι : Type w} {V : BasisOpen C} {U : ι → BasisOpen C}
    (hU : FamilyCovers V U) (s : ∀ i, Sections (germPresheafOn C F) (U i)) :
    GermFamily F V.obj :=
  fun x => (s (Classical.choose (hU.2 x.val x.property))).val
    ⟨x.val, Classical.choose_spec (hU.2 x.val x.property)⟩

/-- Independence of the chosen cover member is equality of already constructed stalk families. -/
theorem germGlueFamily_eq (C : OpenBasis X) (F : RawPresheaf.{u,v} B)
    {ι : Type w} {V : BasisOpen C} {U : ι → BasisOpen C}
    (hU : FamilyCovers V U) (s : ∀ i, Sections (germPresheafOn C F) (U i))
    (hs : Compatible (germPresheafOn C F) U s) (i : ι)
    (x : V.obj) (hxi : x.val ∈ (U i).obj) :
    germGlueFamily C F hU s x = (s i).val ⟨x.val, hxi⟩ :=
  compatible_germSections_value C F U s hs
    (Classical.choose (hU.2 x.val x.property)) i x.val
    (Classical.choose_spec (hU.2 x.val x.property)) hxi

/-- A local original representative from a cover member also represents the glued family. -/
theorem germGlueFamily_locallyRepresented (C : OpenBasis X) (F : RawPresheaf.{u,v} B)
    {ι : Type w} {V : BasisOpen C} {U : ι → BasisOpen C}
    (hU : FamilyCovers V U) (s : ∀ i, Sections (germPresheafOn C F) (U i))
    (hs : Compatible (germPresheafOn C F) U s) :
    LocallyRepresented F V.obj (germGlueFamily C F hU s) := by
  intro x
  obtain ⟨i, hxi⟩ := hU.2 x.val x.property
  obtain ⟨W, hxW, hWi, t, ht⟩ := (s i).property ⟨x.val, hxi⟩
  refine ⟨W, hxW, hWi.trans (hU.1 i), t, ?_⟩
  intro y hy
  exact (ht y hy).trans
    (germGlueFamily_eq C F hU s hs i ⟨y, hU.1 i (hWi hy)⟩ (hWi hy)).symm

/-- The actual glued section, constructed directly without a sheaf assumption on the input. -/
noncomputable def germGlue (C : OpenBasis X) (F : RawPresheaf.{u,v} B)
    {ι : Type w} {V : BasisOpen C} {U : ι → BasisOpen C}
    (hU : FamilyCovers V U) (s : ∀ i, Sections (germPresheafOn C F) (U i))
    (hs : Compatible (germPresheafOn C F) U s) : GermSections F V.obj :=
  ⟨germGlueFamily C F hU s, germGlueFamily_locallyRepresented C F hU s hs⟩

theorem germGlue_restriction (C : OpenBasis X) (F : RawPresheaf.{u,v} B)
    {ι : Type w} {V : BasisOpen C} {U : ι → BasisOpen C}
    (hU : FamilyCovers V U) (s : ∀ i, Sections (germPresheafOn C F) (U i))
    (hs : Compatible (germPresheafOn C F) U s) (i : ι) :
    germRestriction F (hU.1 i) (germGlue C F hU s hs) = s i := by
  apply GermSections.ext
  intro x
  exact germGlueFamily_eq C F hU s hs i ⟨x.val, hU.1 i x.property⟩ x.property

/-- Direct existence and pointwise uniqueness work for independently sized covering families. -/
theorem germPresheafOn_familySheafCondition (C : OpenBasis X)
    (F : RawPresheaf.{u,v} B) : FamilySheafCondition.{u,max u v,w} (germPresheafOn C F) := by
  intro ι V U hU s hs
  refine ⟨germGlue C F hU s hs, (fun i => germGlue_restriction C F hU s hs i), ?_⟩
  intro t ht
  apply GermSections.ext
  intro x
  obtain ⟨i, hxi⟩ := hU.2 x.val x.property
  have heq := congrArg (fun z : GermSections F (U i).obj => z.val ⟨x.val, hxi⟩) (ht i)
  exact heq.trans (germGlueFamily_eq C F hU s hs i x hxi).symm

/-- The direct construction satisfies precisely the published literal set-cover condition. -/
theorem germPresheafOn_sheafCondition (C : OpenBasis X) (F : RawPresheaf.{u,v} B) :
    SheafCondition (germPresheafOn C F) :=
  FamilySheafCondition.sheafCondition (germPresheafOn C F)
    (germPresheafOn_familySheafCondition C F)

/-- The same-family construction is an actual normalized basis presheaf. -/
noncomputable def germNormalizedPresheafOn (C : OpenBasis X)
    (F : RawPresheaf.{u,v} B) : Presheaf.{u,max u v} C :=
  ⟨germPresheafOn C F, germPresheafOn_isNormalized C F⟩

/-- Literal basis sheaf on the target basis, using the original input's stalks. -/
noncomputable def germSheafOn (C : OpenBasis X) (F : RawPresheaf.{u,v} B) :
    BasisSheaf.{u,max u v} C :=
  ⟨germNormalizedPresheafOn C F, germPresheafOn_sheafCondition C F⟩

/-- Pointwise stalk maps form a natural transformation on every target basis. -/
noncomputable def germPresheafMapOn (C : OpenBasis X)
    {F G : RawPresheaf.{u,v} B} (φ : F ⟶ G) :
    germPresheafOn C F ⟶ germPresheafOn C G where
  app U := AddCommGrpCat.ofHom (germSectionsMap φ U.unop.obj)
  naturality _ _ _ := rfl

/-- Functorial literal sheaf packaging, with independent original and target bases. -/
noncomputable def rawGermSheafFunctorOn (B C : OpenBasis X) :
    RawPresheaf.{u,v} B ⥤ BasisSheaf.{u,max u v} C where
  obj F := germSheafOn C F
  map φ := ObjectProperty.homMk (ObjectProperty.homMk (germPresheafMapOn C φ))
  map_id F := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.ext
    intro s
    exact DFunLike.congr_fun (germSectionsMap_id F U.unop.obj) s
  map_comp φ ψ := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.ext
    intro s
    exact DFunLike.congr_fun (germSectionsMap_comp φ ψ U.unop.obj) s

/-- Renard's chosen-basis sheaf construction, extended to raw inputs in the joint universe. -/
noncomputable def rawGermSheafFunctor (B : OpenBasis X) :
    RawPresheaf.{u,v} B ⥤ BasisSheaf.{u,max u v} B :=
  rawGermSheafFunctorOn B B

/-- The source-normalized specialization is composition with the actual existing inclusion. -/
noncomputable def germSheafFunctor (B : OpenBasis X) :
    Presheaf.{u,v} B ⥤ BasisSheaf.{u,max u v} B :=
  presheafInclusion B ⋙ rawGermSheafFunctor B

/-- The canonical basis consisting of all actual opens of the supplied topology. -/
def allOpenBasis (X : Type u) [TopologicalSpace X] : OpenBasis X where
  opens := Set.univ
  isBasis := by
    have h : (fun U : Opens X => (U : Set X)) '' (Set.univ : Set (Opens X)) =
        {S : Set X | IsOpen S} := by
      ext S
      constructor
      · rintro ⟨U, _, rfl⟩
        exact U.isOpen
      · intro hS
        exact ⟨⟨S, hS⟩, Set.mem_univ _, rfl⟩
    rw [h]
    exact isTopologicalBasis_opens

/-- Every actual open as an object of the canonical all-open basis. -/
def allOpen (U : Opens X) : BasisOpen (allOpenBasis X) :=
  ⟨U, Set.mem_univ U⟩

/-- The all-open sheaf uses exactly the same locally represented families as the basis sheaf. -/
noncomputable def rawAllOpenGermSheafFunctor (B : OpenBasis X) :
    RawPresheaf.{u,v} B ⥤ BasisSheaf.{u,max u v} (allOpenBasis X) :=
  rawGermSheafFunctorOn B (allOpenBasis X)

noncomputable def allOpenGermSheafFunctor (B : OpenBasis X) :
    Presheaf.{u,v} B ⥤ BasisSheaf.{u,max u v} (allOpenBasis X) :=
  presheafInclusion B ⋙ rawAllOpenGermSheafFunctor B

@[simp]
theorem rawGermSheafFunctor_sections (F : RawPresheaf.{u,v} B) (U : BasisOpen B) :
    Sections ((rawGermSheafFunctor B).obj F).obj.obj U =
      AddCommGrpCat.of (GermSections F U.obj) := rfl

@[simp]
theorem rawGermSheafFunctor_restriction (F : RawPresheaf.{u,v} B)
    {U V : BasisOpen B} (h : U.obj ≤ V.obj) :
    (restriction ((rawGermSheafFunctor B).obj F).obj.obj h).hom =
      germRestriction F h := rfl

@[simp]
theorem rawAllOpenGermSheafFunctor_sections (F : RawPresheaf.{u,v} B) (U : Opens X) :
    Sections ((rawAllOpenGermSheafFunctor B).obj F).obj.obj (allOpen U) =
      AddCommGrpCat.of (GermSections F U) := rfl

@[simp]
theorem rawAllOpenGermSheafFunctor_restriction (F : RawPresheaf.{u,v} B)
    {U V : Opens X} (h : U ≤ V) :
    (restriction ((rawAllOpenGermSheafFunctor B).obj F).obj.obj
      (U := allOpen U) (V := allOpen V) h).hom = germRestriction F h := rfl

@[simp]
theorem rawGermSheafFunctor_map_app {F G : RawPresheaf.{u,v} B} (φ : F ⟶ G)
    (U : BasisOpen B) :
    (((rawGermSheafFunctor B).map φ).hom.hom.app (op U)).hom =
      germSectionsMap φ U.obj := rfl

@[simp]
theorem rawAllOpenGermSheafFunctor_map_app {F G : RawPresheaf.{u,v} B} (φ : F ⟶ G)
    (U : Opens X) :
    (((rawAllOpenGermSheafFunctor B).map φ).hom.hom.app (op (allOpen U))).hom =
      germSectionsMap φ U := rfl

end Langlands.Sheaf.Renard
