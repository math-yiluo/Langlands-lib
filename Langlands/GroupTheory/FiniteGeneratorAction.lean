import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-! # Actions preserving a finite additive generating set -/

noncomputable section

universe u v w

namespace Langlands.GroupTheory.FiniteGeneratorAction

variable {M : Type u} [AddGroup M] {H : Type v} [Group H]
  (ρ : H →* Multiplicative (M ≃+ M)) (S : Set M)
  (hstable : ∀ h : H, Set.MapsTo (ρ h).toAdd S S)

/-- Restriction of an additive group action to an invariant generating set.
Generation and finiteness are not needed to define this permutation action. -/
def generatorPermutation : H →* Equiv.Perm S where
  toFun h :=
    { toFun := fun x => ⟨(ρ h).toAdd x, hstable h x.property⟩
      invFun := fun x => ⟨(ρ h⁻¹).toAdd x, hstable h⁻¹ x.property⟩
      left_inv := by
        intro x
        apply Subtype.ext
        change (ρ h⁻¹ * ρ h).toAdd x = x
        rw [← map_mul, inv_mul_cancel, map_one]
        rfl
      right_inv := by
        intro x
        apply Subtype.ext
        change (ρ h * ρ h⁻¹).toAdd x = x
        rw [← map_mul, mul_inv_cancel, map_one]
        rfl }
  map_one' := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change (ρ 1).toAdd x = x
    rw [map_one]
    rfl
  map_mul' h g := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change (ρ (h * g)).toAdd x = (ρ h).toAdd ((ρ g).toAdd x)
    rw [map_mul]
    rfl

@[simp]
theorem generatorPermutation_apply (h : H) (x : S) :
    (generatorPermutation ρ S hstable h x : M) = (ρ h).toAdd x := rfl

/-- On an additive generating set, equality of restricted permutations is exactly
equality of the original additive automorphisms. -/
theorem generatorPermutation_eq_iff (hgen : AddSubgroup.closure S = ⊤) (h g : H) :
    generatorPermutation ρ S hstable h = generatorPermutation ρ S hstable g ↔
      ρ h = ρ g := by
  constructor
  · intro heq
    have hhom : (ρ h).toAdd.toAddMonoidHom = (ρ g).toAdd.toAddMonoidHom :=
      AddMonoidHom.eq_of_eqOn_dense hgen fun x hx => by
        exact congrArg (fun e : Equiv.Perm S => (e ⟨x, hx⟩ : M)) heq
    exact congrArg Multiplicative.ofAdd
      (AddEquiv.ext fun x => DFunLike.congr_fun hhom x)
  · intro heq
    apply Equiv.ext
    intro x
    apply Subtype.ext
    exact DFunLike.congr_fun (congrArg Multiplicative.toAdd heq) (x : M)

/-- A faithful action remains faithful after restriction to additive generators. -/
theorem generatorPermutation_injective (hgen : AddSubgroup.closure S = ⊤)
    (hfaith : Function.Injective ρ) :
    Function.Injective (generatorPermutation ρ S hstable) := by
  intro h g heq
  exact hfaith ((generatorPermutation_eq_iff ρ S hstable hgen h g).mp heq)

include hstable in
/-- A group acting faithfully and preserving a finite additive generating set is finite. -/
theorem finite_of_preserves_generating_set (hS : S.Finite)
    (hgen : AddSubgroup.closure S = ⊤) (hfaith : Function.Injective ρ) : Finite H := by
  have : Finite S := hS
  exact Finite.of_injective (generatorPermutation ρ S hstable)
    (generatorPermutation_injective ρ S hstable hgen hfaith)

include hstable in
/-- The image is finite even when the original additive action is not faithful. -/
theorem finite_range_of_preserves_generating_set (hS : S.Finite)
    (hgen : AddSubgroup.closure S = ⊤) : Finite ρ.range := by
  apply finite_of_preserves_generating_set ρ.range.subtype S ?_ hS hgen
    Subtype.val_injective
  intro h
  obtain ⟨g, hg⟩ := h.property
  change Set.MapsTo h.val.toAdd S S
  rw [← hg]
  exact hstable g

section Linear

variable {R : Type w} [Semiring R] {V : Type u} [AddCommGroup V] [Module R V]

/-- Forgetting scalar compatibility gives a faithful homomorphism of automorphism groups. -/
def linearAutToAddAut : (V ≃ₗ[R] V) →* Multiplicative (V ≃+ V) where
  toFun e := Multiplicative.ofAdd e.toAddEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

theorem linearAutToAddAut_injective :
    Function.Injective (linearAutToAddAut (R := R) (V := V)) := by
  intro e f hef
  exact LinearEquiv.ext fun x =>
    DFunLike.congr_fun (congrArg Multiplicative.toAdd hef) x

/-- A subgroup of linear automorphisms preserving a finite additive generating set is finite. -/
theorem finite_linear_subgroup_of_preserves_generating_set
    (K : Subgroup (V ≃ₗ[R] V)) (S : Set V)
    (hstable : ∀ g : K, Set.MapsTo g.val S S)
    (hS : S.Finite) (hgen : AddSubgroup.closure S = ⊤) : Finite K :=
  finite_of_preserves_generating_set
    ((linearAutToAddAut (R := R) (V := V)).comp K.subtype) S hstable hS hgen
    (linearAutToAddAut_injective.comp Subtype.val_injective)

/-- The image of a linear action preserving a finite additive generating set is finite. -/
theorem finite_linear_range_of_preserves_generating_set
    (σ : H →* (V ≃ₗ[R] V)) (S : Set V)
    (hstable : ∀ g : H, Set.MapsTo (σ g) S S)
    (hS : S.Finite) (hgen : AddSubgroup.closure S = ⊤) : Finite σ.range := by
  apply finite_linear_subgroup_of_preserves_generating_set σ.range S ?_ hS hgen
  intro g
  obtain ⟨h, hh⟩ := g.property
  rw [← hh]
  exact hstable h

end Linear

end Langlands.GroupTheory.FiniteGeneratorAction
