import Langlands.Algebra.CentralSimple.LandherrQuadraticData
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.RingTheory.Artinian.Module

/-! # Norm-one scalars avoiding the spectrum of an element -/

noncomputable section

namespace Langlands.CentralSimple.Landherr

open Langlands.GroupScheme.SU3Root

universe u v

variable (F : Type u) (E : Type u) [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] [CharZero F]

/-- The sequence `(k + r) / (k - r)` for natural numbers `k`. Its terms have norm one
when `F` has characteristic zero. -/
def normOneSeq (k : ℕ) : E := ((k : E) + skewRoot F E) / ((k : E) - skewRoot F E)

theorem natCast_add_skewRoot_ne_zero (k : ℕ) : (k : E) + skewRoot F E ≠ 0 := by
  intro h
  apply skewRoot_not_mem_range F E
  exact ⟨-(k : F), by rw [map_neg, map_natCast]; linear_combination -h⟩

theorem natCast_sub_skewRoot_ne_zero (k : ℕ) : (k : E) - skewRoot F E ≠ 0 := by
  intro h
  apply skewRoot_not_mem_range F E
  exact ⟨(k : F), by rw [map_natCast]; linear_combination h⟩

theorem normOneSeq_mul_conj (k : ℕ) :
    normOneSeq F E k * conjugation F E (normOneSeq F E k) = 1 := by
  have h1 := natCast_add_skewRoot_ne_zero F E k
  have h2 := natCast_sub_skewRoot_ne_zero F E k
  rw [normOneSeq, map_div₀, map_add, map_sub, map_natCast, conjugation_skewRoot,
    ← sub_eq_add_neg, sub_neg_eq_add, div_mul_div_comm, mul_comm ((k : E) - skewRoot F E),
    div_self (mul_ne_zero h1 h2)]

theorem normOneSeq_injective : Function.Injective (normOneSeq F E) := by
  intro j k h
  have h2 := natCast_sub_skewRoot_ne_zero F E j
  have h4 := natCast_sub_skewRoot_ne_zero F E k
  rw [normOneSeq, normOneSeq, div_eq_div_iff h2 h4] at h
  have h' : (2 : E) * skewRoot F E * ((k : E) - j) = 0 := by linear_combination h
  have hE : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  rcases mul_eq_zero.mp h' with h0 | h0
  · rcases mul_eq_zero.mp h0 with h00 | h00
    · exact absurd h00 two_ne_zero
    · exact absurd h00 (skewRoot_ne_zero F E)
  · exact_mod_cast (sub_eq_zero.mp h0).symm

variable (B : Type v) [Ring B] [Algebra E B] [FiniteDimensional E B]

/-- Let `E/F` be separable quadratic in characteristic zero. For every `z` in a
finite-dimensional `E`-algebra there is `μ ∈ E` of norm one with `μ - z` invertible.
Only finitely many scalars are eigenvalues of left multiplication by `z`. -/
theorem exists_normOne_isUnit_sub (z : B) :
    ∃ μ : E, μ * conjugation F E μ = 1 ∧ IsUnit (algebraMap E B μ - z) := by
  classical
  have hfin := Module.End.finite_hasEigenvalue (Algebra.lmul E B z)
  have hinf : (Set.range (normOneSeq F E)).Infinite :=
    Set.infinite_range_of_injective (normOneSeq_injective F E)
  obtain ⟨μ, ⟨k, rfl⟩, hμ⟩ := hinf.exists_notMem_finset hfin.toFinset
  refine ⟨normOneSeq F E k, normOneSeq_mul_conj F E k, ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hμ
  have : IsArtinianRing B := IsArtinianRing.of_finite E B
  by_contra hu
  apply hμ
  set c := algebraMap E B (normOneSeq F E k) - z
  have hninj : ¬ Function.Injective (Algebra.lmul E B c) := by
    intro hinj
    have hsurj := LinearMap.surjective_of_injective hinj
    obtain ⟨w, hw⟩ := hsurj 1
    exact hu (isUnit_iff_exists_inv.mpr ⟨w, hw⟩)
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff] at hninj
  push Not at hninj
  obtain ⟨x, hx, hx0⟩ := hninj
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := x) ⟨?_, hx0⟩
  rw [Module.End.mem_eigenspace_iff]
  have hx' : c * x = 0 := hx
  change z * x = normOneSeq F E k • x
  rw [Algebra.smul_def]
  rw [sub_mul, sub_eq_zero] at hx'
  exact hx'.symm

end Langlands.CentralSimple.Landherr
