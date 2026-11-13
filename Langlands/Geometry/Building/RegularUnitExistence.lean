import Langlands.Geometry.Building.MaximalUnramifiedValuation
import Langlands.Galois.Local.SeparableUnramifiedArithmeticProof
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Units `c` with every `c^m - 1` a unit

If the residue field of a valuation is infinite, then for every finite set of positive
exponents `m` there is a unit `c` of the valuation ring such that every `c^m - 1` is again
a unit. The maximal unramified extension of a nonarchimedean local field has an
algebraically closed, hence infinite, residue field.
-/

noncomputable section

universe u

open Polynomial

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

/-- Elements of the valuation ring with nonzero residue have valuation one. -/
theorem valuation_eq_one_of_residue_ne_zero (v : Valuation k Γ) (a : v.valuationSubring)
    (ha : IsLocalRing.residue v.valuationSubring a ≠ 0) : v (a : k) = 1 := by
  have hu : IsUnit a := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff]
    exact ha
  have h1 : v.valuationSubring.valuation (a : k) = 1 :=
    (v.valuationSubring.valuation_eq_one_iff a).mp hu
  have h2 := (Valuation.isEquiv_valuation_valuationSubring v).eq_iff (r := (a : k)) (s := 1)
  rw [map_one, map_one] at h2
  exact h2.mpr h1

/-- **Regular units.** If the residue field of `v` is infinite, then for every finite set `N`
of positive exponents there is a unit `c` with `v c = 1` and `v (c^m - 1) = 1` for every
`m ∈ N`. -/
theorem exists_unit_valuation_pow_sub_one_eq_one (v : Valuation k Γ)
    [Infinite (IsLocalRing.ResidueField v.valuationSubring)] (N : Finset ℕ)
    (hN : ∀ m ∈ N, 0 < m) :
    ∃ c : kˣ, v (c : k) = 1 ∧ ∀ m ∈ N, v ((c : k) ^ m - 1) = 1 := by
  classical
  let κ := IsLocalRing.ResidueField v.valuationSubring
  let bad : Finset κ :=
    insert 0 (N.biUnion fun m => (((X : κ[X]) ^ m - C 1).roots.toFinset))
  obtain ⟨c₀, hc₀⟩ := Infinite.exists_notMem_finset bad
  have hc₀0 : c₀ ≠ 0 := fun h => hc₀ (h ▸ Finset.mem_insert_self _ _)
  have hc₀m : ∀ m ∈ N, c₀ ^ m - 1 ≠ 0 := by
    intro m hm h
    apply hc₀
    refine Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨m, hm, ?_⟩)
    rw [Multiset.mem_toFinset, mem_roots (X_pow_sub_C_ne_zero (hN m hm) 1)]
    simp [h]
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective c₀
  have hva : v (a : k) = 1 := valuation_eq_one_of_residue_ne_zero v a (by rw [ha]; exact hc₀0)
  have ha0 : (a : k) ≠ 0 := by
    intro h
    rw [h, map_zero] at hva
    exact zero_ne_one hva
  refine ⟨Units.mk0 _ ha0, by simpa using hva, fun m hm => ?_⟩
  have h := valuation_eq_one_of_residue_ne_zero v (a ^ m - 1)
    (by rw [map_sub, map_pow, map_one, ha]; exact hc₀m m hm)
  simpa using h

/-- If the residue field of `v` is infinite, some unit has square different from one. -/
theorem exists_unit_sq_ne_one (v : Valuation k Γ)
    [Infinite (IsLocalRing.ResidueField v.valuationSubring)] : ∃ d : kˣ, d ^ 2 ≠ 1 := by
  obtain ⟨c, -, hc⟩ := exists_unit_valuation_pow_sub_one_eq_one v {2} (by simp)
  refine ⟨c, fun h => ?_⟩
  have h2 := hc 2 (Finset.mem_singleton_self 2)
  have : (c : k) ^ 2 - 1 = 0 := by
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one, sub_self]
  rw [this, map_zero] at h2
  exact zero_ne_one h2

end Langlands.Geometry.Building

namespace Langlands.Geometry.Building.MaximalUnramified

open Langlands.LocalGalois.Separable
open scoped ValuativeRel

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The residue field of the integer-valued valuation on the maximal unramified extension
is infinite. -/
theorem infinite_residueField :
    Infinite (IsLocalRing.ResidueField (valuation F).valuationSubring) := by
  let := (residueToFixedField F).toAlgebra
  let : IsAlgClosure 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    fixedFieldResidueIsAlgClosure F
  have : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    IsAlgClosure.isAlgClosed 𝓀[F]
  have hinf : Infinite (IsLocalRing.ResidueField (fixedFieldIntegers F)) := inferInstance
  exact (valuationSubring_eq F).symm ▸ hinf

/-- Regular units of the maximal unramified extension. -/
theorem exists_unit_valuation_pow_sub_one_eq_one (N : Finset ℕ) (hN : ∀ m ∈ N, 0 < m) :
    ∃ c : (inertiaFixedField F)ˣ, valuation F (c : inertiaFixedField F) = 1 ∧
      ∀ m ∈ N, valuation F ((c : inertiaFixedField F) ^ m - 1) = 1 := by
  have := infinite_residueField F
  exact Langlands.Geometry.Building.exists_unit_valuation_pow_sub_one_eq_one
    (valuation F) N hN

/-- The maximal unramified extension has a unit whose square is not one. -/
theorem exists_unit_sq_ne_one : ∃ d : (inertiaFixedField F)ˣ, d ^ 2 ≠ 1 := by
  have := infinite_residueField F
  exact Langlands.Geometry.Building.exists_unit_sq_ne_one (valuation F)

end Langlands.Geometry.Building.MaximalUnramified
