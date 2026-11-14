import Langlands.GroupScheme.Examples.SU3RootNormalizedJumps
import Langlands.GroupScheme.Examples.SU3RootRescaledJumps

/-! # Indivisible coordinate jumps over finite henselian towers -/

noncomputable section

universe u v w

namespace Langlands.GroupScheme.SU3Root

section DiscreteBase

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
  (ω : AddValuation L (WithTop ℝ))

/-- A nontrivial base value group contained in an inverse integer lattice has
an attained positive generator. -/
theorem exists_positive_base_generator (N : ℕ) (hN : 0 < N)
    (hlattice : ∀ a : K, a ≠ 0 →
      ∃ n : ℤ, ω (algebraMap K L a) = (((n : ℝ) / N : ℝ) : WithTop ℝ))
    (hone : ∃ a : K, ω (algebraMap K L a) = ((1 : ℝ) : WithTop ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∃ π : K,
      ω (algebraMap K L π) = (c : WithTop ℝ) ∧
      ∀ a : K, a ≠ 0 →
        ∃ n : ℤ, ω (algebraMap K L a) = (((n : ℝ) * c : ℝ) : WithTop ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let P : ℤ → Prop := fun n => 0 < n ∧
    ∃ a : K, a ≠ 0 ∧ ω (algebraMap K L a) = (((n : ℝ) / N : ℝ) : WithTop ℝ)
  have hinh : ∃ n : ℤ, P n := by
    obtain ⟨a, ha⟩ := hone
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero, ω.map_zero] at ha
      exact WithTop.top_ne_coe ha
    refine ⟨N, by exact_mod_cast hN, a, ha0, ?_⟩
    simpa only [Int.cast_natCast, div_self (ne_of_gt hNR)] using ha
  obtain ⟨m, ⟨hm, π, hπ0, hπ⟩, hmin⟩ := Int.exists_least_of_bdd
    (P := P) ⟨0, fun n hn => le_of_lt hn.1⟩ hinh
  let c : ℝ := (m : ℝ) / N
  have hc : 0 < c := div_pos (by exact_mod_cast hm) hNR
  refine ⟨c, hc, π, hπ, fun a ha0 => ?_⟩
  obtain ⟨n, hn⟩ := hlattice a ha0
  have hπmap : algebraMap K L π ≠ 0 := (map_ne_zero _).mpr hπ0
  have hrem :
      ω (algebraMap K L (a * π ^ (-(n / m)))) =
        ((((n % m : ℤ) : ℝ) / N : ℝ) : WithTop ℝ) := by
    rw [map_mul, map_zpow₀, ω.map_mul, hn,
      omega_zpow ω hπmap c hπ, ← WithTop.coe_add, WithTop.coe_eq_coe]
    have hdecomp : (n : ℝ) = ((n % m : ℤ) : ℝ) +
        (m : ℝ) * ((n / m : ℤ) : ℝ) := by
      exact_mod_cast (Int.emod_add_mul_ediv n m).symm
    dsimp [c]
    push_cast
    field_simp
    nlinarith [hdecomp]
  have hrem0 : n % m = 0 := by
    have hnonneg := Int.emod_nonneg n (ne_of_gt hm)
    have hlt := Int.emod_lt_of_pos n hm
    by_contra h
    have hpos : 0 < n % m := by omega
    have hp : P (n % m) := ⟨hpos, a * π ^ (-(n / m)),
      mul_ne_zero ha0 (zpow_ne_zero _ hπ0), hrem⟩
    have := hmin _ hp
    omega
  refine ⟨n / m, ?_⟩
  rw [hn, WithTop.coe_eq_coe]
  have hdecomp : (n : ℝ) = (m : ℝ) * ((n / m : ℤ) : ℝ) := by
    have hd := Int.emod_add_mul_ediv n m
    rw [hrem0, zero_add] at hd
    exact_mod_cast hd.symm
  dsimp [c]
  rw [hdecomp]
  ring

end DiscreteBase

section Quadratic

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
  [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]

/-- A conjugation-invariant quadratic valuation whose base values lie in an
inverse integer lattice and include one. -/
structure IsLatticeQuadraticValuation (ω : AddValuation L (WithTop ℝ)) : Prop where
  conjugation_eq : ∀ z : L, ω (conjugation K L z) = ω z
  base_lattice : ∃ N : ℕ, 0 < N ∧ ∀ a : K, a ≠ 0 →
    ∃ n : ℤ, ω (algebraMap K L a) = (((n : ℝ) / N : ℝ) : WithTop ℝ)
  exists_one : ∃ π : K, ω (algebraMap K L π) = ((1 : ℝ) : WithTop ℝ)

variable {K L}

namespace IsLatticeQuadraticValuation

variable {ω : AddValuation L (WithTop ℝ)} (hω : IsLatticeQuadraticValuation K L ω)
include hω

/-- The attained positive base generator gives a normalized positive rescaling. -/
theorem exists_normalized_rescale :
    ∃ (a : ℝ) (ha : 0 < a),
      IsNormalizedQuadraticValuation K L (rescaleValuation ω a ha) := by
  obtain ⟨N, hN, hlattice⟩ := hω.base_lattice
  obtain ⟨c, hc, π, hπ, hbase⟩ :=
    exists_positive_base_generator K L ω N hN hlattice hω.exists_one
  refine ⟨c⁻¹, inv_pos.mpr hc, ?_, ?_, π, ?_⟩
  · intro z
    simp only [rescaleValuation_apply, hω.conjugation_eq]
  · intro a ha
    obtain ⟨n, hn⟩ := hbase a ha
    refine ⟨n, ?_⟩
    rw [rescaleValuation_apply, hn, scaleTop_coe, WithTop.coe_eq_coe]
    field_simp
  · rw [rescaleValuation_apply, hπ, scaleTop_coe,
      inv_mul_cancel₀ (ne_of_gt hc)]

/-- The normalized quadratic jump theorem transports back to the original
lattice-valued coordinate valuation. -/
theorem hasIndivisibleCentralJump :
    Parameters.HasIndivisibleCentralJump (c := fieldInvolution K L) ω := by
  obtain ⟨a, ha, hnormalized⟩ := hω.exists_normalized_rescale
  exact (Parameters.hasIndivisibleCentralJump_rescale_iff ω a ha).mp
    hnormalized.hasIndivisibleCentralJump

end IsLatticeQuadraticValuation

end Quadratic

section Tower

variable (k : Type u) (E : Type v) (L : Type w)
  [Field k] [Field E] [Field L]
  [Algebra k E] [Algebra E L] [Algebra k L] [IsScalarTower k E L]
  [Algebra.IsQuadraticExtension E L] [Algebra.IsSeparable E L]
  [Algebra.IsSeparable k L] [FiniteDimensional k E]
  (v : Valuation k (WithZero (Multiplicative ℤ)))
  (hH : HenselianLocalRing v.valuationSubring)
  (hv : Function.Surjective v)

include hv

/-- The original base-normalized valuation of a finite separable quadratic
tower has the required discrete base values. -/
theorem tower_isLatticeQuadraticValuation :
    IsLatticeQuadraticValuation E L
      (FieldTheory.henselianSeparableAddValuation v hH L) := by
  let : FiniteDimensional E L := .of_finrank_pos
    (by rw [Algebra.IsQuadraticExtension.finrank_eq_two E L]; decide)
  let : FiniteDimensional k L := FiniteDimensional.trans k E L
  refine ⟨henselianSeparableAddValuation_quadratic_bar k E L v hH,
    ⟨Module.finrank k L, Module.finrank_pos, ?_⟩, ?_⟩
  · intro a ha
    exact FieldTheory.henselianSeparableAddValuation_exists_lattice_value v hH L
      ((map_ne_zero _).mpr ha)
  · obtain ⟨a, _, ha⟩ := exists_towerValuation_base_eq k L v hH hv 1
    refine ⟨algebraMap k E a, ?_⟩
    simpa only [IsScalarTower.algebraMap_apply k E L, Int.cast_one] using ha

/-- Every finite henselian tower with a separable quadratic top step has an
indivisible central coordinate jump in the original base normalization. -/
theorem tower_hasIndivisibleCentralJump :
    Parameters.HasIndivisibleCentralJump (c := fieldInvolution E L)
      (FieldTheory.henselianSeparableAddValuation v hH L) :=
  (tower_isLatticeQuadraticValuation k E L v hH hv).hasIndivisibleCentralJump

end Tower

end Langlands.GroupScheme.SU3Root
