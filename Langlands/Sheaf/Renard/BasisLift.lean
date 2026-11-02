import Langlands.Sheaf.Renard.BasisSheaf
import Langlands.Sheaf.Renard.BasisStalk
import Mathlib.Algebra.Category.Grp.Ulift

/-!
# Universe lifts of Renard's basis presheaves and basis sheaves

Postcomposition with `AddCommGrpCat.uliftFunctor` moves every section group from the
value universe `v` to `max v w`. The space, its topology, the chosen basis and the basis
opens are unchanged. The space universe `u`, value universe `v`, lift universe `w` and
cover-index universe `w'` are independent.
-/

open CategoryTheory Opposite TopologicalSpace

universe u v w w'

namespace Langlands.Sheaf.Renard

variable {X : Type u} [TopologicalSpace X]

/-! ### The raw lift -/

/-- The raw universe lift: postcomposition with the actual additive `ULift` functor. -/
def rawLift (B : OpenBasis X) : RawPresheaf.{u,v} B ⥤ RawPresheaf.{u,max v w} B :=
  (Functor.whiskeringRight (BasisOpen B)ᵒᵖ AddCommGrpCat.{v} AddCommGrpCat.{max v w}).obj
    AddCommGrpCat.uliftFunctor.{w,v}

theorem rawLift_obj (B : OpenBasis X) (F : RawPresheaf.{u,v} B) :
    (rawLift.{u,v,w} B).obj F = F ⋙ AddCommGrpCat.uliftFunctor.{w,v} := rfl

theorem rawLift_map (B : OpenBasis X) {F G : RawPresheaf.{u,v} B} (φ : F ⟶ G) :
    (rawLift.{u,v,w} B).map φ = Functor.whiskerRight φ AddCommGrpCat.uliftFunctor.{w,v} := rfl

/-- At every basis open the lifted section group is the actual `ULift` group. -/
theorem sections_rawLift {B : OpenBasis X} (F : RawPresheaf.{u,v} B) (U : BasisOpen B) :
    Sections ((rawLift.{u,v,w} B).obj F) U = AddCommGrpCat.of (ULift.{w,v} (Sections F U)) :=
  rfl

/-- The carrier of a lifted section group is literally `ULift` of the original carrier. -/
theorem sections_rawLift_carrier {B : OpenBasis X} (F : RawPresheaf.{u,v} B)
    (U : BasisOpen B) :
    (Sections ((rawLift.{u,v,w} B).obj F) U : Type (max v w)) = ULift.{w,v} (Sections F U) :=
  rfl

/-- Lifted restriction takes `ULift.up s` to the lift of the original restriction. -/
@[simp]
theorem restriction_rawLift_up {B : OpenBasis X} (F : RawPresheaf.{u,v} B)
    {U V : BasisOpen B} (h : U.obj ≤ V.obj) (s : Sections F V) :
    restriction ((rawLift.{u,v,w} B).obj F) h (ULift.up s) = ULift.up (restriction F h s) :=
  rfl

/-- Lowering a lifted restriction is the original restriction of the lowered section. -/
@[simp]
theorem restriction_rawLift_down {B : OpenBasis X} (F : RawPresheaf.{u,v} B)
    {U V : BasisOpen B} (h : U.obj ≤ V.obj) (t : Sections ((rawLift.{u,v,w} B).obj F) V) :
    ULift.down (restriction ((rawLift.{u,v,w} B).obj F) h t) =
      restriction F h (ULift.down t) :=
  rfl

/-- A lifted morphism component takes `ULift.up s` to the lift of the original component. -/
@[simp]
theorem rawLift_map_app_up {B : OpenBasis X} {F G : RawPresheaf.{u,v} B} (φ : F ⟶ G)
    (U : BasisOpen B) (s : Sections F U) :
    ((rawLift.{u,v,w} B).map φ).app (op U) (ULift.up s) = ULift.up (φ.app (op U) s) :=
  rfl

/-- Lowering a lifted morphism component is the original component of the lowered section. -/
@[simp]
theorem rawLift_map_app_down {B : OpenBasis X} {F G : RawPresheaf.{u,v} B} (φ : F ⟶ G)
    (U : BasisOpen B) (t : Sections ((rawLift.{u,v,w} B).obj F) U) :
    ULift.down (((rawLift.{u,v,w} B).map φ).app (op U) t) = φ.app (op U) (ULift.down t) :=
  rfl

theorem rawLift_map_id (B : OpenBasis X) (F : RawPresheaf.{u,v} B) :
    (rawLift.{u,v,w} B).map (𝟙 F) = 𝟙 ((rawLift.{u,v,w} B).obj F) :=
  (rawLift.{u,v,w} B).map_id F

theorem rawLift_map_comp (B : OpenBasis X) {F G H : RawPresheaf.{u,v} B}
    (φ : F ⟶ G) (ψ : G ⟶ H) :
    (rawLift.{u,v,w} B).map (φ ≫ ψ) = (rawLift.{u,v,w} B).map φ ≫ (rawLift.{u,v,w} B).map ψ :=
  (rawLift.{u,v,w} B).map_comp φ ψ

/-! ### Normalization -/

/-- A lifted section group is subsingleton exactly when the original one is. -/
theorem subsingleton_sections_rawLift_iff {B : OpenBasis X} (F : RawPresheaf.{u,v} B)
    (U : BasisOpen B) :
    Subsingleton (Sections ((rawLift.{u,v,w} B).obj F) U) ↔ Subsingleton (Sections F U) :=
  (Equiv.ulift : ULift.{w,v} (Sections F U) ≃ Sections F U).subsingleton_congr

/-- The raw lift preserves and reflects normalization at every empty basis open. -/
theorem isNormalized_rawLift_iff {B : OpenBasis X} (F : RawPresheaf.{u,v} B) :
    IsNormalized ((rawLift.{u,v,w} B).obj F) ↔ IsNormalized F :=
  forall_congr' fun U => imp_congr_right fun _ => subsingleton_sections_rawLift_iff F U

theorem isNormalized_rawLift {B : OpenBasis X} {F : RawPresheaf.{u,v} B}
    (hF : IsNormalized F) : IsNormalized ((rawLift.{u,v,w} B).obj F) :=
  (isNormalized_rawLift_iff F).2 hF

theorem isNormalized_of_rawLift {B : OpenBasis X} {F : RawPresheaf.{u,v} B}
    (hF : IsNormalized ((rawLift.{u,v,w} B).obj F)) : IsNormalized F :=
  (isNormalized_rawLift_iff F).1 hF

/-- The normalized lift: the raw lift restricted to normalized basis presheaves. -/
def presheafLift (B : OpenBasis X) : Presheaf.{u,v} B ⥤ Presheaf.{u,max v w} B :=
  ObjectProperty.lift _ (presheafInclusion.{u,v} B ⋙ rawLift.{u,v,w} B)
    fun F => (isNormalized_rawLift_iff F.obj).2 F.property

theorem presheafLift_obj_obj (B : OpenBasis X) (F : Presheaf.{u,v} B) :
    ((presheafLift.{u,v,w} B).obj F).obj = (rawLift.{u,v,w} B).obj F.obj := rfl

theorem presheafLift_map_hom (B : OpenBasis X) {F G : Presheaf.{u,v} B} (φ : F ⟶ G) :
    ((presheafLift.{u,v,w} B).map φ).hom = (rawLift.{u,v,w} B).map φ.hom := rfl

/-- Erasing normalization after the normalized lift is the raw lift after erasure. -/
theorem presheafLift_comp_inclusion (B : OpenBasis X) :
    presheafLift.{u,v,w} B ⋙ presheafInclusion.{u,max v w} B =
      presheafInclusion.{u,v} B ⋙ rawLift.{u,v,w} B :=
  rfl

/-- The same commutation as an isomorphism with identity components. -/
def presheafLiftCompInclusionIso (B : OpenBasis X) :
    presheafLift.{u,v,w} B ⋙ presheafInclusion.{u,max v w} B ≅
      presheafInclusion.{u,v} B ⋙ rawLift.{u,v,w} B :=
  Iso.refl _

@[simp]
theorem presheafLiftCompInclusionIso_hom_app (B : OpenBasis X) (F : Presheaf.{u,v} B) :
    (presheafLiftCompInclusionIso.{u,v,w} B).hom.app F = 𝟙 ((rawLift.{u,v,w} B).obj F.obj) :=
  rfl

@[simp]
theorem presheafLiftCompInclusionIso_inv_app (B : OpenBasis X) (F : Presheaf.{u,v} B) :
    (presheafLiftCompInclusionIso.{u,v,w} B).inv.app F = 𝟙 ((rawLift.{u,v,w} B).obj F.obj) :=
  rfl

/-! ### Gluing -/

section Gluing

variable {B : OpenBasis X} (F : RawPresheaf.{u,v} B) {ι : Type w'}

/-- Lifting a family by `ULift.up` preserves and reflects literal compatibility. -/
theorem compatible_rawLift_up_iff (U : ι → BasisOpen B) (s : ∀ i, Sections F (U i)) :
    Compatible ((rawLift.{u,v,w} B).obj F) U (fun i => ULift.up (s i)) ↔ Compatible F U s := by
  constructor
  · intro h i j W hWi hWj
    exact congrArg ULift.down (h i j W hWi hWj)
  · intro h i j W hWi hWj
    exact congrArg ULift.up (h i j W hWi hWj)

/-- Lowering a lifted family by `ULift.down` preserves and reflects literal compatibility. -/
theorem compatible_rawLift_iff (U : ι → BasisOpen B)
    (s : ∀ i, Sections ((rawLift.{u,v,w} B).obj F) (U i)) :
    Compatible ((rawLift.{u,v,w} B).obj F) U s ↔ Compatible F U (fun i => ULift.down (s i)) := by
  constructor
  · intro h i j W hWi hWj
    exact congrArg ULift.down (h i j W hWi hWj)
  · intro h i j W hWi hWj
    exact congrArg ULift.up (h i j W hWi hWj)

/-- A lifted section amalgamates a lifted family exactly when the lowerings do. -/
theorem isAmalgamation_rawLift_iff {V : BasisOpen B} {U : ι → BasisOpen B}
    (hU : FamilyCovers V U) (s : ∀ i, Sections ((rawLift.{u,v,w} B).obj F) (U i))
    (t : Sections ((rawLift.{u,v,w} B).obj F) V) :
    IsAmalgamation ((rawLift.{u,v,w} B).obj F) hU s t ↔
      IsAmalgamation F hU (fun i => ULift.down (s i)) (ULift.down t) := by
  constructor
  · intro h i
    exact congrArg ULift.down (h i)
  · intro h i
    exact congrArg ULift.up (h i)

/-- The lift of a section amalgamates the lifted family exactly when it amalgamates. -/
theorem isAmalgamation_rawLift_up_iff {V : BasisOpen B} {U : ι → BasisOpen B}
    (hU : FamilyCovers V U) (s : ∀ i, Sections F (U i)) (t : Sections F V) :
    IsAmalgamation ((rawLift.{u,v,w} B).obj F) hU (fun i => ULift.up (s i)) (ULift.up t) ↔
      IsAmalgamation F hU s t :=
  isAmalgamation_rawLift_iff F hU (fun i => ULift.up (s i)) (ULift.up t)

/-- Unique gluing of a lifted family is equivalent to unique gluing of its lowering. -/
theorem existsUnique_isAmalgamation_rawLift_iff {V : BasisOpen B} {U : ι → BasisOpen B}
    (hU : FamilyCovers V U) (s : ∀ i, Sections ((rawLift.{u,v,w} B).obj F) (U i)) :
    (∃! t : Sections ((rawLift.{u,v,w} B).obj F) V,
        IsAmalgamation ((rawLift.{u,v,w} B).obj F) hU s t) ↔
      ∃! t : Sections F V, IsAmalgamation F hU (fun i => ULift.down (s i)) t := by
  constructor
  · rintro ⟨t, ht, huniq⟩
    refine ⟨ULift.down t, (isAmalgamation_rawLift_iff F hU s t).1 ht, fun y hy => ?_⟩
    exact congrArg ULift.down
      (huniq (ULift.up y) ((isAmalgamation_rawLift_iff F hU s (ULift.up y)).2 hy))
  · rintro ⟨t, ht, huniq⟩
    refine ⟨ULift.up t, (isAmalgamation_rawLift_iff F hU s (ULift.up t)).2 ht, fun y hy => ?_⟩
    exact congrArg ULift.up (huniq (ULift.down y) ((isAmalgamation_rawLift_iff F hU s y).1 hy))

/-- The arbitrary-index source condition is preserved and reflected in every index universe. -/
theorem familySheafCondition_rawLift_iff :
    FamilySheafCondition.{u,max v w,w'} ((rawLift.{u,v,w} B).obj F) ↔
      FamilySheafCondition.{u,v,w'} F := by
  constructor
  · intro h ι V U hU s hs
    exact (existsUnique_isAmalgamation_rawLift_iff F hU (fun i => ULift.up (s i))).1
      (h ι V U hU _ ((compatible_rawLift_up_iff F U s).2 hs))
  · intro h ι V U hU s hs
    exact (existsUnique_isAmalgamation_rawLift_iff F hU s).2
      (h ι V U hU _ ((compatible_rawLift_iff F U s).1 hs))

/-- The raw lift preserves and reflects the literal set-cover sheaf condition. -/
theorem sheafCondition_rawLift_iff :
    SheafCondition ((rawLift.{u,v,w} B).obj F) ↔ SheafCondition F :=
  (sheafCondition_iff_family _).trans
    ((familySheafCondition_rawLift_iff F).trans (sheafCondition_iff_family F).symm)

variable {F}

theorem sheafCondition_rawLift (hF : SheafCondition F) :
    SheafCondition ((rawLift.{u,v,w} B).obj F) :=
  (sheafCondition_rawLift_iff F).2 hF

theorem sheafCondition_of_rawLift (hF : SheafCondition ((rawLift.{u,v,w} B).obj F)) :
    SheafCondition F :=
  (sheafCondition_rawLift_iff F).1 hF

end Gluing

/-- The basis-sheaf lift: the normalized lift restricted to basis sheaves. -/
def sheafLift (B : OpenBasis X) : BasisSheaf.{u,v} B ⥤ BasisSheaf.{u,max v w} B :=
  ObjectProperty.lift _ (sheafForget.{u,v} B ⋙ presheafLift.{u,v,w} B)
    fun F => (sheafCondition_rawLift_iff F.obj.obj).2 F.property

theorem sheafLift_obj_obj (B : OpenBasis X) (F : BasisSheaf.{u,v} B) :
    ((sheafLift.{u,v,w} B).obj F).obj = (presheafLift.{u,v,w} B).obj F.obj := rfl

theorem sheafLift_obj_obj_obj (B : OpenBasis X) (F : BasisSheaf.{u,v} B) :
    ((sheafLift.{u,v,w} B).obj F).obj.obj = (rawLift.{u,v,w} B).obj F.obj.obj := rfl

theorem sheafLift_map_hom (B : OpenBasis X) {F G : BasisSheaf.{u,v} B} (φ : F ⟶ G) :
    ((sheafLift.{u,v,w} B).map φ).hom = (presheafLift.{u,v,w} B).map φ.hom := rfl

theorem sheafLift_map_hom_hom (B : OpenBasis X) {F G : BasisSheaf.{u,v} B} (φ : F ⟶ G) :
    ((sheafLift.{u,v,w} B).map φ).hom.hom = (rawLift.{u,v,w} B).map φ.hom.hom := rfl

/-- Erasing the sheaf condition after the sheaf lift is the normalized lift. -/
theorem sheafLift_comp_forget (B : OpenBasis X) :
    sheafLift.{u,v,w} B ⋙ sheafForget.{u,max v w} B =
      sheafForget.{u,v} B ⋙ presheafLift.{u,v,w} B :=
  rfl

/-- Erasing both conditions after the sheaf lift is the raw lift. -/
theorem sheafLift_comp_forget_comp_inclusion (B : OpenBasis X) :
    sheafLift.{u,v,w} B ⋙ sheafForget.{u,max v w} B ⋙ presheafInclusion.{u,max v w} B =
      sheafForget.{u,v} B ⋙ presheafInclusion.{u,v} B ⋙ rawLift.{u,v,w} B :=
  rfl

/-- The normalized erasure as an isomorphism with identity components. -/
def sheafLiftCompForgetIso (B : OpenBasis X) :
    sheafLift.{u,v,w} B ⋙ sheafForget.{u,max v w} B ≅
      sheafForget.{u,v} B ⋙ presheafLift.{u,v,w} B :=
  Iso.refl _

@[simp]
theorem sheafLiftCompForgetIso_hom_app (B : OpenBasis X) (F : BasisSheaf.{u,v} B) :
    (sheafLiftCompForgetIso.{u,v,w} B).hom.app F = 𝟙 ((presheafLift.{u,v,w} B).obj F.obj) :=
  rfl

@[simp]
theorem sheafLiftCompForgetIso_inv_app (B : OpenBasis X) (F : BasisSheaf.{u,v} B) :
    (sheafLiftCompForgetIso.{u,v,w} B).inv.app F = 𝟙 ((presheafLift.{u,v,w} B).obj F.obj) :=
  rfl

/-- The raw erasure as an isomorphism with identity components. -/
def sheafLiftCompRawIso (B : OpenBasis X) :
    sheafLift.{u,v,w} B ⋙ sheafForget.{u,max v w} B ⋙ presheafInclusion.{u,max v w} B ≅
      sheafForget.{u,v} B ⋙ presheafInclusion.{u,v} B ⋙ rawLift.{u,v,w} B :=
  Iso.refl _

@[simp]
theorem sheafLiftCompRawIso_hom_app (B : OpenBasis X) (F : BasisSheaf.{u,v} B) :
    (sheafLiftCompRawIso.{u,v,w} B).hom.app F = 𝟙 ((rawLift.{u,v,w} B).obj F.obj.obj) :=
  rfl

@[simp]
theorem sheafLiftCompRawIso_inv_app (B : OpenBasis X) (F : BasisSheaf.{u,v} B) :
    (sheafLiftCompRawIso.{u,v,w} B).inv.app F = 𝟙 ((rawLift.{u,v,w} B).obj F.obj.obj) :=
  rfl

/-- A lifted basis sheaf glues every compatible family indexed by any type `ι : Type w'`;
the gluing section lowers to the original gluing of the lowered family. -/
theorem sheafLift_unique_gluing {B : OpenBasis X} (F : BasisSheaf.{u,v} B) {ι : Type w'}
    (V : BasisOpen B) (U : ι → BasisOpen B) (hU : FamilyCovers V U)
    (s : ∀ i, Sections ((rawLift.{u,v,w} B).obj F.obj.obj) (U i))
    (hs : Compatible ((rawLift.{u,v,w} B).obj F.obj.obj) U s) :
    ∃! t : Sections ((rawLift.{u,v,w} B).obj F.obj.obj) V,
      IsAmalgamation F.obj.obj hU (fun i => ULift.down (s i)) (ULift.down t) := by
  obtain ⟨t, ht, huniq⟩ := ((sheafLift.{u,v,w} B).obj F).unique_gluing V U hU s hs
  refine ⟨t, (isAmalgamation_rawLift_iff F.obj.obj hU s t).1 ht, fun y hy => huniq y ?_⟩
  exact (isAmalgamation_rawLift_iff F.obj.obj hU s y).2 hy

/-! ### Full faithfulness and lowering of morphisms -/

/-- The raw lift is fully faithful, by whiskering Mathlib's fully faithful `ULift` functor. -/
def rawLiftFullyFaithful (B : OpenBasis X) : (rawLift.{u,v,w} B).FullyFaithful :=
  AddCommGrpCat.uliftFunctorFullyFaithful.{v,w}.whiskeringRight (BasisOpen B)ᵒᵖ

instance (B : OpenBasis X) : (rawLift.{u,v,w} B).Full := (rawLiftFullyFaithful B).full

instance (B : OpenBasis X) : (rawLift.{u,v,w} B).Faithful := (rawLiftFullyFaithful B).faithful

/-- Lower a morphism between lifted raw presheaves to the original presheaves. -/
def rawLower {B : OpenBasis X} {F G : RawPresheaf.{u,v} B}
    (φ : (rawLift.{u,v,w} B).obj F ⟶ (rawLift.{u,v,w} B).obj G) : F ⟶ G :=
  (rawLiftFullyFaithful B).preimage φ

/-- The lowered component is `s ↦ (φ.app (op U) (ULift.up s)).down`. -/
@[simp]
theorem rawLower_app_apply {B : OpenBasis X} {F G : RawPresheaf.{u,v} B}
    (φ : (rawLift.{u,v,w} B).obj F ⟶ (rawLift.{u,v,w} B).obj G) (U : BasisOpen B)
    (s : Sections F U) :
    (rawLower φ).app (op U) s = ULift.down (φ.app (op U) (ULift.up s)) :=
  rfl

@[simp]
theorem rawLift_map_rawLower {B : OpenBasis X} {F G : RawPresheaf.{u,v} B}
    (φ : (rawLift.{u,v,w} B).obj F ⟶ (rawLift.{u,v,w} B).obj G) :
    (rawLift.{u,v,w} B).map (rawLower φ) = φ :=
  (rawLiftFullyFaithful B).map_preimage φ

@[simp]
theorem rawLower_rawLift_map {B : OpenBasis X} {F G : RawPresheaf.{u,v} B} (ψ : F ⟶ G) :
    rawLower ((rawLift.{u,v,w} B).map ψ) = ψ :=
  (rawLiftFullyFaithful B).preimage_map ψ

/-- Lower a morphism between lifted normalized presheaves. -/
def presheafLower {B : OpenBasis X} {F G : Presheaf.{u,v} B}
    (φ : (presheafLift.{u,v,w} B).obj F ⟶ (presheafLift.{u,v,w} B).obj G) : F ⟶ G :=
  ObjectProperty.homMk (rawLower (F := F.obj) (G := G.obj) φ.hom)

@[simp]
theorem presheafLower_app_apply {B : OpenBasis X} {F G : Presheaf.{u,v} B}
    (φ : (presheafLift.{u,v,w} B).obj F ⟶ (presheafLift.{u,v,w} B).obj G) (U : BasisOpen B)
    (s : Sections F.obj U) :
    (presheafLower φ).hom.app (op U) s = ULift.down (φ.hom.app (op U) (ULift.up s)) :=
  rfl

@[simp]
theorem presheafLift_map_presheafLower {B : OpenBasis X} {F G : Presheaf.{u,v} B}
    (φ : (presheafLift.{u,v,w} B).obj F ⟶ (presheafLift.{u,v,w} B).obj G) :
    (presheafLift.{u,v,w} B).map (presheafLower φ) = φ :=
  ObjectProperty.hom_ext _ (rawLift_map_rawLower (F := F.obj) (G := G.obj) φ.hom)

@[simp]
theorem presheafLower_presheafLift_map {B : OpenBasis X} {F G : Presheaf.{u,v} B}
    (ψ : F ⟶ G) : presheafLower ((presheafLift.{u,v,w} B).map ψ) = ψ :=
  ObjectProperty.hom_ext _ (rawLower_rawLift_map ψ.hom)

/-- The normalized lift is fully faithful. -/
def presheafLiftFullyFaithful (B : OpenBasis X) : (presheafLift.{u,v,w} B).FullyFaithful where
  preimage φ := presheafLower φ
  map_preimage φ := presheafLift_map_presheafLower φ
  preimage_map ψ := presheafLower_presheafLift_map ψ

instance (B : OpenBasis X) : (presheafLift.{u,v,w} B).Full := (presheafLiftFullyFaithful B).full

instance (B : OpenBasis X) : (presheafLift.{u,v,w} B).Faithful :=
  (presheafLiftFullyFaithful B).faithful

/-- Lower a morphism between lifted basis sheaves. -/
def sheafLower {B : OpenBasis X} {F G : BasisSheaf.{u,v} B}
    (φ : (sheafLift.{u,v,w} B).obj F ⟶ (sheafLift.{u,v,w} B).obj G) : F ⟶ G :=
  ObjectProperty.homMk (presheafLower (F := F.obj) (G := G.obj) φ.hom)

@[simp]
theorem sheafLower_app_apply {B : OpenBasis X} {F G : BasisSheaf.{u,v} B}
    (φ : (sheafLift.{u,v,w} B).obj F ⟶ (sheafLift.{u,v,w} B).obj G) (U : BasisOpen B)
    (s : Sections F.obj.obj U) :
    (sheafLower φ).hom.hom.app (op U) s = ULift.down (φ.hom.hom.app (op U) (ULift.up s)) :=
  rfl

@[simp]
theorem sheafLift_map_sheafLower {B : OpenBasis X} {F G : BasisSheaf.{u,v} B}
    (φ : (sheafLift.{u,v,w} B).obj F ⟶ (sheafLift.{u,v,w} B).obj G) :
    (sheafLift.{u,v,w} B).map (sheafLower φ) = φ :=
  ObjectProperty.hom_ext _ (presheafLift_map_presheafLower (F := F.obj) (G := G.obj) φ.hom)

@[simp]
theorem sheafLower_sheafLift_map {B : OpenBasis X} {F G : BasisSheaf.{u,v} B}
    (ψ : F ⟶ G) : sheafLower ((sheafLift.{u,v,w} B).map ψ) = ψ :=
  ObjectProperty.hom_ext _ (presheafLower_presheafLift_map ψ.hom)

/-- The basis-sheaf lift is fully faithful. -/
def sheafLiftFullyFaithful (B : OpenBasis X) : (sheafLift.{u,v,w} B).FullyFaithful where
  preimage φ := sheafLower φ
  map_preimage φ := sheafLift_map_sheafLower φ
  preimage_map ψ := sheafLower_sheafLift_map ψ

instance (B : OpenBasis X) : (sheafLift.{u,v,w} B).Full := (sheafLiftFullyFaithful B).full

instance (B : OpenBasis X) : (sheafLift.{u,v,w} B).Faithful := (sheafLiftFullyFaithful B).faithful

/-! ### Lifting an already lifted value universe again -/

/-- At value universe `max v w`, lifting again at level `w` is isomorphic to the identity.
Each component is the pointwise additive `ULift.down`, with inverse `ULift.up`. -/
def rawRelift (B : OpenBasis X) : rawLift.{u,max v w,w} B ≅ 𝟭 (RawPresheaf.{u,max v w} B) :=
  NatIso.ofComponents
    (fun F => NatIso.ofComponents
      (fun U => AddEquiv.toAddCommGrpIso (X := ((rawLift.{u,max v w,w} B).obj F).obj U)
        (Y := F.obj U) AddEquiv.ulift)
      (fun _ => rfl))
    (fun _ => rfl)

theorem rawRelift_hom_app_app (B : OpenBasis X) (F : RawPresheaf.{u,max v w} B)
    (U : BasisOpen B) :
    ((rawRelift.{u,v,w} B).hom.app F).app (op U) =
      AddCommGrpCat.ofHom (AddEquiv.ulift : ULift.{w,max v w} (Sections F U) ≃+ _).toAddMonoidHom :=
  rfl

theorem rawRelift_inv_app_app (B : OpenBasis X) (F : RawPresheaf.{u,max v w} B)
    (U : BasisOpen B) :
    ((rawRelift.{u,v,w} B).inv.app F).app (op U) =
      AddCommGrpCat.ofHom
        (AddEquiv.ulift : ULift.{w,max v w} (Sections F U) ≃+ _).symm.toAddMonoidHom :=
  rfl

@[simp]
theorem rawRelift_hom_app_app_apply (B : OpenBasis X) (F : RawPresheaf.{u,max v w} B)
    (U : BasisOpen B) (t : Sections ((rawLift.{u,max v w,w} B).obj F) U) :
    ((rawRelift.{u,v,w} B).hom.app F).app (op U) t = ULift.down t :=
  rfl

@[simp]
theorem rawRelift_inv_app_app_apply (B : OpenBasis X) (F : RawPresheaf.{u,max v w} B)
    (U : BasisOpen B) (s : Sections F U) :
    ((rawRelift.{u,v,w} B).inv.app F).app (op U) s = ULift.up s :=
  rfl

theorem rawRelift_hom_naturality (B : OpenBasis X) {F G : RawPresheaf.{u,max v w} B}
    (φ : F ⟶ G) :
    (rawLift.{u,max v w,w} B).map φ ≫ (rawRelift.{u,v,w} B).hom.app G =
      (rawRelift.{u,v,w} B).hom.app F ≫ φ :=
  (rawRelift.{u,v,w} B).hom.naturality φ

theorem rawRelift_hom_naturality_apply (B : OpenBasis X) {F G : RawPresheaf.{u,max v w} B}
    (φ : F ⟶ G) (U : BasisOpen B) (t : Sections ((rawLift.{u,max v w,w} B).obj F) U) :
    ((rawRelift.{u,v,w} B).hom.app G).app (op U) (((rawLift.{u,max v w,w} B).map φ).app (op U) t) =
      φ.app (op U) (((rawRelift.{u,v,w} B).hom.app F).app (op U) t) :=
  rfl

/-- The normalized re-lift isomorphism, with the raw components. -/
def presheafRelift (B : OpenBasis X) :
    presheafLift.{u,max v w,w} B ≅ 𝟭 (Presheaf.{u,max v w} B) :=
  NatIso.ofComponents (fun F => ObjectProperty.isoMk _ ((rawRelift.{u,v,w} B).app F.obj))
    (fun φ => ObjectProperty.hom_ext _ ((rawRelift.{u,v,w} B).hom.naturality φ.hom))

theorem presheafRelift_hom_app_hom (B : OpenBasis X) (F : Presheaf.{u,max v w} B) :
    ((presheafRelift.{u,v,w} B).hom.app F).hom = (rawRelift.{u,v,w} B).hom.app F.obj :=
  rfl

theorem presheafRelift_inv_app_hom (B : OpenBasis X) (F : Presheaf.{u,max v w} B) :
    ((presheafRelift.{u,v,w} B).inv.app F).hom = (rawRelift.{u,v,w} B).inv.app F.obj :=
  rfl

@[simp]
theorem presheafRelift_hom_app_hom_app_apply (B : OpenBasis X) (F : Presheaf.{u,max v w} B)
    (U : BasisOpen B) (t : Sections ((rawLift.{u,max v w,w} B).obj F.obj) U) :
    ((presheafRelift.{u,v,w} B).hom.app F).hom.app (op U) t = ULift.down t :=
  rfl

@[simp]
theorem presheafRelift_inv_app_hom_app_apply (B : OpenBasis X) (F : Presheaf.{u,max v w} B)
    (U : BasisOpen B) (s : Sections F.obj U) :
    ((presheafRelift.{u,v,w} B).inv.app F).hom.app (op U) s = ULift.up s :=
  rfl

theorem presheafRelift_hom_naturality (B : OpenBasis X) {F G : Presheaf.{u,max v w} B}
    (φ : F ⟶ G) :
    (presheafLift.{u,max v w,w} B).map φ ≫ (presheafRelift.{u,v,w} B).hom.app G =
      (presheafRelift.{u,v,w} B).hom.app F ≫ φ :=
  (presheafRelift.{u,v,w} B).hom.naturality φ

/-- The basis-sheaf re-lift isomorphism, with the raw components. -/
def sheafRelift (B : OpenBasis X) :
    sheafLift.{u,max v w,w} B ≅ 𝟭 (BasisSheaf.{u,max v w} B) :=
  NatIso.ofComponents (fun F => ObjectProperty.isoMk _ ((presheafRelift.{u,v,w} B).app F.obj))
    (fun φ => ObjectProperty.hom_ext _ ((presheafRelift.{u,v,w} B).hom.naturality φ.hom))

theorem sheafRelift_hom_app_hom (B : OpenBasis X) (F : BasisSheaf.{u,max v w} B) :
    ((sheafRelift.{u,v,w} B).hom.app F).hom = (presheafRelift.{u,v,w} B).hom.app F.obj :=
  rfl

theorem sheafRelift_inv_app_hom (B : OpenBasis X) (F : BasisSheaf.{u,max v w} B) :
    ((sheafRelift.{u,v,w} B).inv.app F).hom = (presheafRelift.{u,v,w} B).inv.app F.obj :=
  rfl

theorem sheafRelift_hom_app_hom_hom (B : OpenBasis X) (F : BasisSheaf.{u,max v w} B) :
    ((sheafRelift.{u,v,w} B).hom.app F).hom.hom = (rawRelift.{u,v,w} B).hom.app F.obj.obj :=
  rfl

theorem sheafRelift_inv_app_hom_hom (B : OpenBasis X) (F : BasisSheaf.{u,max v w} B) :
    ((sheafRelift.{u,v,w} B).inv.app F).hom.hom = (rawRelift.{u,v,w} B).inv.app F.obj.obj :=
  rfl

@[simp]
theorem sheafRelift_hom_app_hom_hom_app_apply (B : OpenBasis X) (F : BasisSheaf.{u,max v w} B)
    (U : BasisOpen B) (t : Sections ((rawLift.{u,max v w,w} B).obj F.obj.obj) U) :
    ((sheafRelift.{u,v,w} B).hom.app F).hom.hom.app (op U) t = ULift.down t :=
  rfl

@[simp]
theorem sheafRelift_inv_app_hom_hom_app_apply (B : OpenBasis X) (F : BasisSheaf.{u,max v w} B)
    (U : BasisOpen B) (s : Sections F.obj.obj U) :
    ((sheafRelift.{u,v,w} B).inv.app F).hom.hom.app (op U) s = ULift.up s :=
  rfl

theorem sheafRelift_hom_naturality (B : OpenBasis X) {F G : BasisSheaf.{u,max v w} B}
    (φ : F ⟶ G) :
    (sheafLift.{u,max v w,w} B).map φ ≫ (sheafRelift.{u,v,w} B).hom.app G =
      (sheafRelift.{u,v,w} B).hom.app F ≫ φ :=
  (sheafRelift.{u,v,w} B).hom.naturality φ

/-- The normalized re-lift erases to the raw re-lift. -/
theorem presheafRelift_erasure (B : OpenBasis X) :
    Functor.isoWhiskerRight (presheafRelift.{u,v,w} B) (presheafInclusion.{u,max v w} B) =
      Functor.isoWhiskerLeft (presheafInclusion.{u,max v w} B) (rawRelift.{u,v,w} B) :=
  rfl

/-- The basis-sheaf re-lift erases to the normalized re-lift. -/
theorem sheafRelift_erasure (B : OpenBasis X) :
    Functor.isoWhiskerRight (sheafRelift.{u,v,w} B) (sheafForget.{u,max v w} B) =
      Functor.isoWhiskerLeft (sheafForget.{u,max v w} B) (presheafRelift.{u,v,w} B) :=
  rfl

/-- The basis-sheaf re-lift erases through both inclusions to the raw re-lift. -/
theorem sheafRelift_erasure_raw (B : OpenBasis X) :
    Functor.isoWhiskerRight (sheafRelift.{u,v,w} B)
        (sheafForget.{u,max v w} B ⋙ presheafInclusion.{u,max v w} B) =
      Functor.isoWhiskerLeft (sheafForget.{u,max v w} B ⋙ presheafInclusion.{u,max v w} B)
        (rawRelift.{u,v,w} B) :=
  rfl

/-! ### The joint value universe `max u v` -/

/-- Lift level `u` sends `v`-valued raw presheaves to the joint value universe `max u v`. -/
abbrev rawLiftJoint (B : OpenBasis X) : RawPresheaf.{u,v} B ⥤ RawPresheaf.{u,max u v} B :=
  rawLift.{u,v,u} B

/-- Lift level `u` for normalized presheaves. -/
abbrev presheafLiftJoint (B : OpenBasis X) : Presheaf.{u,v} B ⥤ Presheaf.{u,max u v} B :=
  presheafLift.{u,v,u} B

/-- Lift level `u` for basis sheaves. -/
abbrev sheafLiftJoint (B : OpenBasis X) : BasisSheaf.{u,v} B ⥤ BasisSheaf.{u,max u v} B :=
  sheafLift.{u,v,u} B

/-- The lifted stalk diagram is the neighborhood restriction of the joint raw lift. -/
theorem stalkDiagram_eq_rawLiftJoint {B : OpenBasis X} (F : RawPresheaf.{u,v} B) (x : X) :
    stalkDiagram F x = neighborhoodInclusion B x ⋙ (rawLiftJoint B).obj F :=
  rfl

/-- At the joint value universe, lifting again at level `u` is isomorphic to the identity. -/
abbrev rawReliftJoint (B : OpenBasis X) :
    rawLift.{u,max u v,u} B ≅ 𝟭 (RawPresheaf.{u,max u v} B) :=
  rawRelift.{u,v,u} B

/-- The normalized joint re-lift isomorphism. -/
abbrev presheafReliftJoint (B : OpenBasis X) :
    presheafLift.{u,max u v,u} B ≅ 𝟭 (Presheaf.{u,max u v} B) :=
  presheafRelift.{u,v,u} B

/-- The basis-sheaf joint re-lift isomorphism. -/
abbrev sheafReliftJoint (B : OpenBasis X) :
    sheafLift.{u,max u v,u} B ≅ 𝟭 (BasisSheaf.{u,max u v} B) :=
  sheafRelift.{u,v,u} B

end Langlands.Sheaf.Renard
