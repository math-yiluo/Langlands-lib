import Langlands.GroupScheme.ImageGenerationNoetherian
import Langlands.GroupScheme.RepresentabilityTransfer

/-! # Closed submonoids with Noetherian affine squares are subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ImageGeneration

variable {B : Scheme.{u}}

/-- The shear automorphism `(x, y) ↦ (x, x y)` of the square of a group scheme. -/
def shearIso (G : GroupScheme B) : G.X ⊗ G.X ≅ G.X ⊗ G.X where
  hom := lift (fst _ _) (fst _ _ * snd _ _)
  inv := lift (fst _ _) ((fst _ _)⁻¹ * snd _ _)
  hom_inv_id := by
    apply hom_ext
    · simp
    · rw [Category.assoc, lift_snd, MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd,
        Category.id_comp, inv_mul_cancel_left]
  inv_hom_id := by
    apply hom_ext
    · simp
    · rw [Category.assoc, lift_snd, MonObj.comp_mul, lift_fst, lift_snd, Category.id_comp,
        mul_inv_cancel_left]

set_option backward.isDefEq.respectTransparency.types false in
/-- The tensor product of two morphisms whose underlying morphisms are closed immersions
has a closed immersion as underlying morphism. -/
theorem isClosedImmersion_tensorHom_left {X X' Y Y' : Over B} (a : X ⟶ X') (b : Y ⟶ Y')
    [IsClosedImmersion a.left] [IsClosedImmersion b.left] :
    IsClosedImmersion (a ⊗ₘ b).left := by
  rw [Over.tensorHom_left]
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion) ‹_› ‹_›
    (Over.w a).symm (Over.w b).symm

variable {G : GroupScheme B} {Z : Over B} (j : Z ⟶ G.X) [IsClosedImmersion j.left]
  (m : Z ⊗ Z ⟶ Z) (hm : m ≫ j = (fst Z Z ≫ j) * (snd Z Z ≫ j))

/-- The restricted shear endomorphism `(x, y) ↦ (x, x y)` of `Z × Z`. -/
def shear : Z ⊗ Z ⟶ Z ⊗ Z := lift (fst Z Z) m

omit [IsClosedImmersion j.left] in
include hm in
theorem shear_comp : shear m ≫ (j ⊗ₘ j) = (j ⊗ₘ j) ≫ (shearIso G).hom := by
  apply hom_ext
  · simp [shear, shearIso]
  · rw [Category.assoc, tensorHom_snd, shear, lift_snd_assoc, hm, Category.assoc, shearIso,
      lift_snd, MonObj.comp_mul, tensorHom_fst, tensorHom_snd]

include hm in
/-- The restricted shear is an isomorphism when `Z × Z` is Noetherian and affine: it is a
closed immersion of that scheme into itself. -/
theorem isIso_shear [IsAffine (Z ⊗ Z).left] [IsLocallyNoetherian (Z ⊗ Z).left] :
    IsIso (shear m) := by
  have : IsClosedImmersion (j ⊗ₘ j).left := isClosedImmersion_tensorHom_left j j
  have : IsClosedImmersion ((shear m).left ≫ (j ⊗ₘ j).left) := by
    rw [← Over.comp_left, shear_comp j m hm, Over.comp_left]
    have : IsIso (shearIso G).hom.left :=
      (inferInstance : IsIso ((Over.forget B).map (shearIso G).hom))
    infer_instance
  have : IsClosedImmersion (shear m).left :=
    IsClosedImmersion.of_comp_isClosedImmersion _ (j ⊗ₘ j).left
  have : IsIso ((Over.forget B).map (shear m)) := isIso_of_isClosedImmersion_endo (shear m).left
  exact isIso_of_reflects_iso _ (Over.forget B)

variable (e : 𝟙_ (Over B) ⟶ Z) (he : e ≫ j = 1)

include hm he in
/-- The inverse of a point of `Z` again factors through `Z`. -/
theorem exists_inv_factor [IsAffine (Z ⊗ Z).left] [IsLocallyNoetherian (Z ⊗ Z).left]
    {T : Over B} (x : T ⟶ Z) : ∃ y : T ⟶ Z, y ≫ j = (x ≫ j)⁻¹ := by
  have := isIso_shear j m hm
  let u := lift x (toUnit T ≫ e) ≫ inv (shear m)
  have hu : u ≫ shear m = lift x (toUnit T ≫ e) := by simp [u]
  have h1 : u ≫ fst Z Z = x := by
    have := congrArg (· ≫ fst Z Z) hu
    simpa [shear] using this
  have h2 : u ≫ m = toUnit T ≫ e := by
    have := congrArg (· ≫ snd Z Z) hu
    simpa [shear] using this
  refine ⟨u ≫ snd Z Z, eq_inv_of_mul_eq_one_right ?_⟩
  have h3 := congrArg (· ≫ j) h2
  simp only [Category.assoc, hm, MonObj.comp_mul, he, MonObj.comp_one] at h3
  rw [← h1, Category.assoc, Category.assoc]
  exact h3

theorem mono_of_isClosedImmersion_left : Mono j := Over.mono_of_mono_left j

variable [IsAffine (Z ⊗ Z).left] [IsLocallyNoetherian (Z ⊗ Z).left]

/-- The subgroup functor of points factoring through a closed submonoid `Z`. -/
def closedSubgroupFunctor : SubgroupFunctor G where
  carrier T :=
    { carrier := {x | ∃ y : T ⟶ Z, y ≫ j = x}
      one_mem' := ⟨toUnit T ≫ e, by rw [Category.assoc, he, MonObj.comp_one]⟩
      mul_mem' := by
        rintro _ _ ⟨y, rfl⟩ ⟨y', rfl⟩
        exact ⟨lift y y' ≫ m, by
          rw [Category.assoc, hm, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]⟩
      inv_mem' := by
        rintro _ ⟨y, rfl⟩
        exact exists_inv_factor j m hm e he y }
  comp_mem a := by
    rintro _ ⟨y, rfl⟩
    exact ⟨a ≫ y, Category.assoc _ _ _⟩

theorem mem_closedSubgroupFunctor {T : Over B} {x : T ⟶ G.X} :
    x ∈ (closedSubgroupFunctor j m hm e he).carrier T ↔ ∃ y : T ⟶ Z, y ≫ j = x :=
  Iff.rfl

/-- The actual group scheme carried by the closed submonoid `Z`. -/
abbrev closedSubgroup : GroupScheme B :=
  haveI := mono_of_isClosedImmersion_left j
  (closedSubgroupFunctor j m hm e he).representingGroupScheme j fun _ _ => Iff.rfl

theorem closedSubgroup_X : (closedSubgroup j m hm e he).X = Z := rfl

/-- The inclusion of the closed submonoid as an actual group-scheme homomorphism. -/
def closedSubgroupHom : closedSubgroup j m hm e he ⟶ G :=
  haveI := mono_of_isClosedImmersion_left j
  (closedSubgroupFunctor j m hm e he).representingHom j fun _ _ => Iff.rfl

@[simp] theorem closedSubgroupHom_hom : (closedSubgroupHom j m hm e he).hom.hom = j :=
  haveI := mono_of_isClosedImmersion_left j
  (closedSubgroupFunctor j m hm e he).representingHom_hom j fun _ _ => Iff.rfl

theorem isClosedSubgroup_closedSubgroupHom :
    IsClosedSubgroup (closedSubgroupHom j m hm e he) := by
  unfold IsClosedSubgroup
  rw [closedSubgroupHom_hom]
  infer_instance

end Langlands.GroupScheme.ImageGeneration
