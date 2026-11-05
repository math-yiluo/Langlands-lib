import Langlands.Sheaf.Renard.LocallyConstantScalarSheaf
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Original-universe comparison of Renard all-open sheaves with Mathlib
-/

open CategoryTheory Opposite TopologicalSpace

universe u v w

noncomputable section

namespace Langlands.Sheaf.Renard.AllOpenMathlib

variable {X : Type u} [TopologicalSpace X]

/-- The existing all-open lift followed by inclusion returns the original open. -/
@[simp] theorem allOpen_obj (W : BasisOpen (allOpenBasis X)) : allOpen W.obj = W := rfl

/-- Precompose a raw source presheaf with the existing lift of all opens. -/
def rawToMathlib (X : Type u) [TopologicalSpace X] :
    RawPresheaf.{u,v} (allOpenBasis X) ⥤
      TopCat.Presheaf AddCommGrpCat.{v} (TopCat.of X) where
  obj F := (LocallyConstantScalar.allOpenFunctor X).op ⋙ F
  map φ := Functor.whiskerLeft (LocallyConstantScalar.allOpenFunctor X).op φ

/-- Restrict an actual Mathlib presheaf along the existing basis inclusion. -/
def rawFromMathlib (X : Type u) [TopologicalSpace X] :
    TopCat.Presheaf AddCommGrpCat.{v} (TopCat.of X) ⥤
      RawPresheaf.{u,v} (allOpenBasis X) where
  obj G := (basisInclusion (allOpenBasis X)).op ⋙ G
  map φ := Functor.whiskerLeft (basisInclusion (allOpenBasis X)).op φ

@[simp] theorem rawToMathlib_obj (F : RawPresheaf.{u,v} (allOpenBasis X)) (U : Opens X) :
    ((rawToMathlib X).obj F).obj (op U) = Sections F (allOpen U) := rfl

@[simp] theorem rawToMathlib_restriction (F : RawPresheaf.{u,v} (allOpenBasis X))
    {U V : Opens X} (h : U ≤ V) :
    ((rawToMathlib X).obj F).map (homOfLE h).op =
      restriction F (U := allOpen U) (V := allOpen V) h := rfl

@[simp] theorem rawToMathlib_map_app {F G : RawPresheaf.{u,v} (allOpenBasis X)}
    (φ : F ⟶ G) (U : Opens X) :
    ((rawToMathlib X).map φ).app (op U) = φ.app (op (allOpen U)) := rfl

@[simp] theorem rawFromMathlib_obj
    (G : TopCat.Presheaf AddCommGrpCat.{v} (TopCat.of X))
    (W : BasisOpen (allOpenBasis X)) :
    Sections ((rawFromMathlib X).obj G) W = G.obj (op W.obj) := rfl

@[simp] theorem rawFromMathlib_restriction
    (G : TopCat.Presheaf AddCommGrpCat.{v} (TopCat.of X))
    {U V : BasisOpen (allOpenBasis X)} (h : U.obj ≤ V.obj) :
    restriction ((rawFromMathlib X).obj G) h = G.map (homOfLE h).op := rfl

@[simp] theorem rawFromMathlib_map_app
    {F G : TopCat.Presheaf AddCommGrpCat.{v} (TopCat.of X)} (φ : F ⟶ G)
    (W : BasisOpen (allOpenBasis X)) :
    ((rawFromMathlib X).map φ).app (op W) = φ.app (op W.obj) := rfl

@[simp] theorem rawToMathlib_map_id (F : RawPresheaf.{u,v} (allOpenBasis X)) :
    (rawToMathlib X).map (𝟙 F) = 𝟙 ((rawToMathlib X).obj F) := rfl

@[simp] theorem rawToMathlib_map_comp {F G H : RawPresheaf.{u,v} (allOpenBasis X)}
    (φ : F ⟶ G) (ψ : G ⟶ H) :
    (rawToMathlib X).map (φ ≫ ψ) = (rawToMathlib X).map φ ≫ (rawToMathlib X).map ψ := rfl

@[simp] theorem rawFromMathlib_map_id
    (F : TopCat.Presheaf AddCommGrpCat.{v} (TopCat.of X)) :
    (rawFromMathlib X).map (𝟙 F) = 𝟙 ((rawFromMathlib X).obj F) := rfl

@[simp] theorem rawFromMathlib_map_comp
    {F G H : TopCat.Presheaf AddCommGrpCat.{v} (TopCat.of X)} (φ : F ⟶ G) (ψ : G ⟶ H) :
    (rawFromMathlib X).map (φ ≫ ψ) = (rawFromMathlib X).map φ ≫ (rawFromMathlib X).map ψ := rfl

/-- The raw round trip is identified with the source by identity section maps. -/
def rawUnitIso (X : Type u) [TopologicalSpace X] :
    𝟭 (RawPresheaf.{u,v} (allOpenBasis X)) ≅ rawToMathlib X ⋙ rawFromMathlib X :=
  NatIso.ofComponents
    (fun F => NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro U V f
      change F.map f ≫ 𝟙 _ = 𝟙 _ ≫ F.map _
      rw [Category.comp_id, Category.id_comp]))
    (by intro F G φ; ext U; rfl)

/-- The raw round trip is identified with Mathlib by identity section maps. -/
def rawCounitIso (X : Type u) [TopologicalSpace X] :
    rawFromMathlib X ⋙ rawToMathlib X ≅
      𝟭 (TopCat.Presheaf AddCommGrpCat.{v} (TopCat.of X)) :=
  NatIso.ofComponents
    (fun G => NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro U V f
      change G.map _ ≫ 𝟙 _ = 𝟙 _ ≫ G.map f
      rw [Category.comp_id, Category.id_comp]))
    (by intro F G φ; ext U; rfl)

/-- Source compatibility on all smaller opens is exactly compatibility on intersections. -/
theorem compatible_iff (F : RawPresheaf.{u,v} (allOpenBasis X))
    {ι : Type w} (U : ι → BasisOpen (allOpenBasis X))
    (s : ∀ i, Sections F (U i)) :
    Compatible F U s ↔
      TopCat.Presheaf.IsCompatible ((rawToMathlib X).obj F ⋙ forget AddCommGrpCat)
        (fun i => (U i).obj) s := by
  constructor
  · intro hs i j
    exact hs i j (allOpen ((U i).obj ⊓ (U j).obj)) inf_le_left inf_le_right
  · intro hs i j W hWi hWj
    have hW : W.obj ≤ (U i).obj ⊓ (U j).obj := le_inf hWi hWj
    have hij : restriction F (U := allOpen ((U i).obj ⊓ (U j).obj)) inf_le_left (s i) =
        restriction F (U := allOpen ((U i).obj ⊓ (U j).obj)) inf_le_right (s j) := hs i j
    have h := congrArg (restriction F (U := W)
      (V := allOpen ((U i).obj ⊓ (U j).obj)) hW) hij
    have hi := restriction_comp_apply F (U := W)
      (V := allOpen ((U i).obj ⊓ (U j).obj)) (W := U i) hW inf_le_left (s i)
    have hj := restriction_comp_apply F (U := W)
      (V := allOpen ((U i).obj ⊓ (U j).obj)) (W := U j) hW inf_le_right (s j)
    exact hi.symm.trans (h.trans hj)

/-- The union of a family is covered by that family, including an empty family. -/
theorem familyCovers_iSup {ι : Type w} (U : ι → BasisOpen (allOpenBasis X)) :
    FamilyCovers (allOpen (⨆ i, (U i).obj)) U := by
  refine ⟨fun i => le_iSup (fun i => (U i).obj) i, ?_⟩
  intro x hx
  exact Opens.mem_iSup.mp hx

/-- Source unique gluing gives the actual Type-valued unique-gluing predicate. -/
theorem uniqueGluing_of_sheafCondition (F : RawPresheaf.{u,v} (allOpenBasis X))
    (hF : SheafCondition F) :
    TopCat.Presheaf.IsSheafUniqueGluing ((rawToMathlib X).obj F ⋙ forget AddCommGrpCat) := by
  intro ι U s hs
  exact SheafCondition.family F hF ι (allOpen (iSup U)) (fun i => allOpen (U i))
    (familyCovers_iSup (fun i => allOpen (U i))) s
    ((compatible_iff F (fun i => allOpen (U i)) s).mpr hs)

/-- The actual Type-valued gluing condition gives the source set-cover axiom. -/
theorem sheafCondition_of_uniqueGluing (F : RawPresheaf.{u,v} (allOpenBasis X))
    (hF : TopCat.Presheaf.IsSheafUniqueGluing
      ((rawToMathlib X).obj F ⋙ forget AddCommGrpCat)) : SheafCondition F := by
  intro V C s hs
  let U : C.members → Opens X := fun i => i.val.obj
  have hsup : iSup U = V.obj := by
    refine le_antisymm (iSup_le (fun i : C.members => C.le i.val i.property)) ?_
    intro x hx
    obtain ⟨W, hW, hxW⟩ := C.covers x hx
    exact Opens.mem_iSup.mpr ⟨⟨W, hW⟩, hxW⟩
  have hglue := hF U s ((compatible_iff F (fun i : C.members => i.val) s).mp hs)
  change ∃! t : Sections F (allOpen (iSup U)),
    ∀ i, restriction F (U := i.val) (V := allOpen (iSup U)) (le_iSup U i) t = s i at hglue
  have hV : allOpen (iSup U) = V := by rw [hsup]; rfl
  obtain ⟨t, ht, huniq⟩ := hglue
  refine ⟨transportSection F hV t, ?_, ?_⟩
  · intro i
    exact (restriction_transport F hV (le_iSup U i) (C.le i.val i.property) t).trans (ht i)
  · intro y hy
    have hy' : transportSection F hV.symm y = t := by
      apply huniq
      intro i
      exact (restriction_transport F hV.symm (C.le i.val i.property) (le_iSup U i) y).trans (hy i)
    have hcancel : ∀ {A B : BasisOpen (allOpenBasis X)} (h : A = B) (z : Sections F B),
        transportSection F h (transportSection F h.symm z) = z := by
      intro A B h z
      cases h
      rfl
    exact (hcancel hV y).symm.trans (congrArg (transportSection F hV) hy')

/-- Sheafhood is detected on underlying sets without existence-of-limits premises. -/
theorem isSheaf_iff_underlying
    (G : TopCat.Presheaf AddCommGrpCat.{v} (TopCat.of X)) :
    TopCat.Presheaf.IsSheaf G ↔ TopCat.Presheaf.IsSheaf (G ⋙ forget AddCommGrpCat) := by
  exact ⟨CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf
      (Opens.grothendieckTopology (TopCat.of X)) G (forget AddCommGrpCat),
    CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp
      (Opens.grothendieckTopology (TopCat.of X)) G (forget AddCommGrpCat)⟩

/-- Literal source gluing is exactly Mathlib's actual site sheaf condition. -/
theorem sheafCondition_iff (F : RawPresheaf.{u,v} (allOpenBasis X)) :
    SheafCondition F ↔ TopCat.Presheaf.IsSheaf ((rawToMathlib X).obj F) := by
  rw [isSheaf_iff_underlying, TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types]
  exact ⟨uniqueGluing_of_sheafCondition F, sheafCondition_of_uniqueGluing F⟩

/-- Pulling back an actual Mathlib sheaf satisfies the literal source axiom. -/
theorem fromMathlib_sheafCondition
    (G : TopCat.Presheaf AddCommGrpCat.{v} (TopCat.of X)) (hG : TopCat.Presheaf.IsSheaf G) :
    SheafCondition ((rawFromMathlib X).obj G) :=
  (sheafCondition_iff _).mpr
    (TopCat.Presheaf.isSheaf_of_iso ((rawCounitIso X).app G).symm hG)

/-- Empty normalization is a consequence of genuine gluing in the Mathlib sheaf. -/
theorem fromMathlib_isNormalized
    (G : TopCat.Presheaf AddCommGrpCat.{v} (TopCat.of X)) (hG : TopCat.Presheaf.IsSheaf G) :
    IsNormalized ((rawFromMathlib X).obj G) :=
  SheafCondition.isNormalized _ (fromMathlib_sheafCondition G hG)

/-- The original-section forward functor on the two actual sheaf categories. -/
def toMathlib (X : Type u) [TopologicalSpace X] :
    BasisSheaf.{u,v} (allOpenBasis X) ⥤ TopCat.Sheaf AddCommGrpCat.{v} (TopCat.of X) where
  obj F := ⟨(rawToMathlib X).obj F.obj.obj, (sheafCondition_iff _).mp F.property⟩
  map φ := ObjectProperty.homMk ((rawToMathlib X).map φ.hom.hom)

/-- The reverse functor, with normalization deduced rather than assumed. -/
def fromMathlib (X : Type u) [TopologicalSpace X] :
    TopCat.Sheaf AddCommGrpCat.{v} (TopCat.of X) ⥤ BasisSheaf.{u,v} (allOpenBasis X) where
  obj G := ⟨⟨(rawFromMathlib X).obj G.obj, fromMathlib_isNormalized G.obj G.property⟩,
    fromMathlib_sheafCondition G.obj G.property⟩
  map φ := ObjectProperty.homMk (ObjectProperty.homMk ((rawFromMathlib X).map φ.hom))

@[simp] theorem toMathlib_sections (F : BasisSheaf.{u,v} (allOpenBasis X)) (U : Opens X) :
    ((toMathlib X).obj F).obj.obj (op U) = Sections F.obj.obj (allOpen U) := rfl

@[simp] theorem toMathlib_restriction (F : BasisSheaf.{u,v} (allOpenBasis X))
    {U V : Opens X} (h : U ≤ V) :
    ((toMathlib X).obj F).obj.map (homOfLE h).op =
      restriction F.obj.obj (U := allOpen U) (V := allOpen V) h := rfl

@[simp] theorem toMathlib_map_app {F G : BasisSheaf.{u,v} (allOpenBasis X)}
    (φ : F ⟶ G) (U : Opens X) :
    ((toMathlib X).map φ).hom.app (op U) = φ.hom.hom.app (op (allOpen U)) := rfl

@[simp] theorem fromMathlib_sections (G : TopCat.Sheaf AddCommGrpCat.{v} (TopCat.of X))
    (W : BasisOpen (allOpenBasis X)) :
    Sections ((fromMathlib X).obj G).obj.obj W = G.obj.obj (op W.obj) := rfl

@[simp] theorem fromMathlib_restriction (G : TopCat.Sheaf AddCommGrpCat.{v} (TopCat.of X))
    {U V : BasisOpen (allOpenBasis X)} (h : U.obj ≤ V.obj) :
    restriction ((fromMathlib X).obj G).obj.obj h = G.obj.map (homOfLE h).op := rfl

@[simp] theorem fromMathlib_map_app
    {F G : TopCat.Sheaf AddCommGrpCat.{v} (TopCat.of X)} (φ : F ⟶ G)
    (W : BasisOpen (allOpenBasis X)) :
    ((fromMathlib X).map φ).hom.hom.app (op W) = φ.hom.app (op W.obj) := rfl

/-- Forward comparison commutes with the existing forgetful inclusions. -/
theorem toMathlib_forget (X : Type u) [TopologicalSpace X] :
    toMathlib.{u,v} X ⋙ TopCat.Sheaf.forget AddCommGrpCat (TopCat.of X) =
      sheafForget (allOpenBasis X) ⋙ presheafInclusion (allOpenBasis X) ⋙ rawToMathlib X := rfl

/-- Reverse comparison commutes with the existing forgetful inclusions. -/
theorem fromMathlib_forget (X : Type u) [TopologicalSpace X] :
    fromMathlib.{u,v} X ⋙ sheafForget (allOpenBasis X) ⋙ presheafInclusion (allOpenBasis X) =
      TopCat.Sheaf.forget AddCommGrpCat (TopCat.of X) ⋙ rawFromMathlib X := rfl

/-- Unit with the original identity section maps through both source subcategories. -/
def unitIso (X : Type u) [TopologicalSpace X] :
    𝟭 (BasisSheaf.{u,v} (allOpenBasis X)) ≅ toMathlib X ⋙ fromMathlib X :=
  NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _ (ObjectProperty.isoMk _ ((rawUnitIso X).app F.obj.obj)))
    (by
      intro F G φ
      apply ObjectProperty.hom_ext _
      apply ObjectProperty.hom_ext _
      ext U
      rfl)

/-- Counit with the original identity section maps in Mathlib's actual sheaf category. -/
def counitIso (X : Type u) [TopologicalSpace X] :
    fromMathlib X ⋙ toMathlib X ≅ 𝟭 (TopCat.Sheaf AddCommGrpCat.{v} (TopCat.of X)) :=
  NatIso.ofComponents
    (fun G => ObjectProperty.isoMk _ ((rawCounitIso X).app G.obj))
    (by
      intro F G φ
      apply CategoryTheory.Sheaf.hom_ext
      ext U
      rfl)

/-- The actual equivalence at the independent original section universe. -/
def equivalence (X : Type u) [TopologicalSpace X] :
    BasisSheaf.{u,v} (allOpenBasis X) ≌ TopCat.Sheaf AddCommGrpCat.{v} (TopCat.of X) where
  functor := toMathlib X
  inverse := fromMathlib X
  unitIso := unitIso X
  counitIso := counitIso X
  functor_unitIso_comp F := by
    apply CategoryTheory.Sheaf.hom_ext
    ext U
    rfl

/-- Arbitrarily indexed gluing still uses the original Mathlib section groups and maps. -/
theorem fromMathlib_unique_gluing (G : TopCat.Sheaf AddCommGrpCat.{v} (TopCat.of X))
    {ι : Type w} (V : BasisOpen (allOpenBasis X)) (U : ι → BasisOpen (allOpenBasis X))
    (hU : FamilyCovers V U) (s : ∀ i, G.obj.obj (op (U i).obj))
    (hs : Compatible ((rawFromMathlib X).obj G.obj) U s) :
    ∃! t : G.obj.obj (op V.obj), ∀ i, G.obj.map (homOfLE (hU.1 i)).op t = s i :=
  SheafCondition.family _ (fromMathlib_sheafCondition G.obj G.property) ι V U hU s hs

@[simp] theorem unit_hom_raw (F : BasisSheaf.{u,v} (allOpenBasis X)) :
    ((unitIso X).hom.app F).hom.hom = ((rawUnitIso X).app F.obj.obj).hom := rfl

@[simp] theorem unit_inv_raw (F : BasisSheaf.{u,v} (allOpenBasis X)) :
    ((unitIso X).inv.app F).hom.hom = ((rawUnitIso X).app F.obj.obj).inv := rfl

@[simp] theorem counit_hom_raw (G : TopCat.Sheaf AddCommGrpCat.{v} (TopCat.of X)) :
    ((counitIso X).hom.app G).hom = ((rawCounitIso X).app G.obj).hom := rfl

@[simp] theorem counit_inv_raw (G : TopCat.Sheaf AddCommGrpCat.{v} (TopCat.of X)) :
    ((counitIso X).inv.app G).hom = ((rawCounitIso X).app G.obj).inv := rfl

/-- After the canonical all-open identification, the unit is the original identity. -/
@[simp] theorem unit_hom_app (F : BasisSheaf.{u,v} (allOpenBasis X))
    (W : BasisOpen (allOpenBasis X)) :
    (((unitIso X).hom.app F).hom.hom).app (op W) = 𝟙 (Sections F.obj.obj W) := rfl

@[simp] theorem unit_inv_app (F : BasisSheaf.{u,v} (allOpenBasis X))
    (W : BasisOpen (allOpenBasis X)) :
    (((unitIso X).inv.app F).hom.hom).app (op W) = 𝟙 (Sections F.obj.obj W) := rfl

@[simp] theorem counit_hom_app (G : TopCat.Sheaf AddCommGrpCat.{v} (TopCat.of X))
    (U : Opens X) :
    (((counitIso X).hom.app G).hom).app (op U) = 𝟙 (G.obj.obj (op U)) := rfl

@[simp] theorem counit_inv_app (G : TopCat.Sheaf AddCommGrpCat.{v} (TopCat.of X))
    (U : Opens X) :
    (((counitIso X).inv.app G).hom).app (op U) = 𝟙 (G.obj.obj (op U)) := rfl

@[simp] theorem unit_hom_apply (F : BasisSheaf.{u,v} (allOpenBasis X))
    (W : BasisOpen (allOpenBasis X)) (s : Sections F.obj.obj W) :
    (((unitIso X).hom.app F).hom.hom).app (op W) s = s := rfl

@[simp] theorem unit_inv_apply (F : BasisSheaf.{u,v} (allOpenBasis X))
    (W : BasisOpen (allOpenBasis X)) (s : Sections F.obj.obj W) :
    (((unitIso X).inv.app F).hom.hom).app (op W) s = s := rfl

@[simp] theorem counit_hom_apply (G : TopCat.Sheaf AddCommGrpCat.{v} (TopCat.of X))
    (U : Opens X) (s : G.obj.obj (op U)) :
    (((counitIso X).hom.app G).hom).app (op U) s = s := rfl

@[simp] theorem counit_inv_apply (G : TopCat.Sheaf AddCommGrpCat.{v} (TopCat.of X))
    (U : Opens X) (s : G.obj.obj (op U)) :
    (((counitIso X).inv.app G).hom).app (op U) s = s := rfl

/-- Naturality identifies the actual original source natural transformations. -/
theorem unit_naturality {F G : BasisSheaf.{u,v} (allOpenBasis X)} (φ : F ⟶ G) :
    φ ≫ (unitIso X).hom.app G =
      (unitIso X).hom.app F ≫ (fromMathlib X).map ((toMathlib X).map φ) :=
  (unitIso X).hom.naturality φ

theorem unit_inv_naturality {F G : BasisSheaf.{u,v} (allOpenBasis X)} (φ : F ⟶ G) :
    (fromMathlib X).map ((toMathlib X).map φ) ≫ (unitIso X).inv.app G =
      (unitIso X).inv.app F ≫ φ :=
  (unitIso X).inv.naturality φ

/-- Naturality identifies the actual original Mathlib natural transformations. -/
theorem counit_naturality {F G : TopCat.Sheaf AddCommGrpCat.{v} (TopCat.of X)}
    (φ : F ⟶ G) :
    (toMathlib X).map ((fromMathlib X).map φ) ≫ (counitIso X).hom.app G =
      (counitIso X).hom.app F ≫ φ :=
  (counitIso X).hom.naturality φ

theorem counit_inv_naturality {F G : TopCat.Sheaf AddCommGrpCat.{v} (TopCat.of X)}
    (φ : F ⟶ G) :
    φ ≫ (counitIso X).inv.app G =
      (counitIso X).inv.app F ≫ (toMathlib X).map ((fromMathlib X).map φ) :=
  (counitIso X).inv.naturality φ

@[simp] theorem unit_hom_inv_id (F : BasisSheaf.{u,v} (allOpenBasis X)) :
    (unitIso X).hom.app F ≫ (unitIso X).inv.app F = 𝟙 F :=
  ((unitIso X).app F).hom_inv_id

@[simp] theorem unit_inv_hom_id (F : BasisSheaf.{u,v} (allOpenBasis X)) :
    (unitIso X).inv.app F ≫ (unitIso X).hom.app F =
      𝟙 ((fromMathlib X).obj ((toMathlib X).obj F)) :=
  ((unitIso X).app F).inv_hom_id

@[simp] theorem counit_hom_inv_id (G : TopCat.Sheaf AddCommGrpCat.{v} (TopCat.of X)) :
    (counitIso X).hom.app G ≫ (counitIso X).inv.app G =
      𝟙 ((toMathlib X).obj ((fromMathlib X).obj G)) :=
  ((counitIso X).app G).hom_inv_id

@[simp] theorem counit_inv_hom_id (G : TopCat.Sheaf AddCommGrpCat.{v} (TopCat.of X)) :
    (counitIso X).inv.app G ≫ (counitIso X).hom.app G = 𝟙 G :=
  ((counitIso X).app G).inv_hom_id

/-- The equivalence coherence law holds for the specified, unchanged functors. -/
@[simp] theorem functor_triangle (F : BasisSheaf.{u,v} (allOpenBasis X)) :
    (toMathlib X).map ((unitIso X).hom.app F) ≫
      (counitIso X).hom.app ((toMathlib X).obj F) = 𝟙 ((toMathlib X).obj F) :=
  (equivalence X).functor_unitIso_comp F

@[simp] theorem inverse_triangle (G : TopCat.Sheaf AddCommGrpCat.{v} (TopCat.of X)) :
    (unitIso X).hom.app ((fromMathlib X).obj G) ≫
      (fromMathlib X).map ((counitIso X).hom.app G) = 𝟙 ((fromMathlib X).obj G) :=
  (equivalence X).unit_inverse_comp G

end Langlands.Sheaf.Renard.AllOpenMathlib
