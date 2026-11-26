import Langlands.Global.FiniteConstantCurveChart
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Finiteness.Cardinality

/-! # Additive quotient of the overlap of the normalized parameter charts -/

noncomputable section

universe u

open AlgebraicCurve IntermediateField Polynomial
open scoped AlgebraicCurve.CurveModel IntermediateField.algebraAdjoinAdjoin

namespace Langlands.Global

variable (k F : Type u) [Field k] [Field F] [Algebra k F] (s : F)

/-- The space of sums of functions on the two actual normalized parameter charts. -/
def curveChartSum : Submodule k F :=
  (CurveModel.chartRing k ({s} : Set F)).toSubmodule ⊔
    (CurveModel.chartRing k ({s⁻¹} : Set F)).toSubmodule

/-- The image of functions on the overlap modulo functions from the two charts. -/
def curveChartAdditiveQuotient : Submodule k (F ⧸ curveChartSum k F s) :=
  (CurveModel.chartRing k ({s, s⁻¹} : Set F)).toSubmodule.map (curveChartSum k F s).mkQ

variable [Finite k] [FiniteDimensional k⟮s⟯ F]

set_option maxHeartbeats 1000000 in
/-- The quotient of the overlap over a finite constant field is finite. -/
theorem finite_curveChartAdditiveQuotient (hs : s ≠ 0) :
    Finite (curveChartAdditiveQuotient k F s) := by
  classical
  let A := Algebra.adjoin k ({s} : Set F)
  let B := CurveModel.chartRing k ({s} : Set F)
  let C := CurveModel.chartRing k ({s⁻¹} : Set F)
  let D := CurveModel.chartRing k ({s, s⁻¹} : Set F)
  let W := curveChartSum k F s
  let q := W.mkQ
  let : Module.Finite A B := FiniteConstantCurveChart.moduleFinite k F s
  have hAB : Function.Injective (algebraMap A B) := fun _ _ h => by
    apply Subtype.ext
    exact congrArg (fun c : B => (c : F)) h
  let : Module.IsTorsionFree A B := Module.isTorsionFree_iff_algebraMap_injective.mpr hAB
  let : Module.Free A B := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis A B
  let : Fintype (Module.Free.ChooseBasisIndex A B) := Fintype.ofFinite _
  have hC : ∀ i, ∃ m : ℕ, (s⁻¹)^m * (b i : F) ∈ C := by
    intro i
    have h : (b i : F) ∈ D := (CurveModel.incl₀ k s (b i)).property
    have h' : (b i : F) ∈ CurveModel.chartRing k (insert (s⁻¹)⁻¹ ({s⁻¹} : Set F)) := by
      simpa only [inv_inv] using h
    exact CurveModel.exists_pow_mul_mem_chartRing (K := k) (Set.mem_singleton s⁻¹)
      (inv_ne_zero hs) h'
  choose m hm using hC
  let g : (Σ i, Fin (m i + 1)) → F ⧸ W := fun j => q ((s⁻¹)^j.2.val * (b j.1 : F))
  let V := Submodule.span k (Set.range g)
  let : Module.Finite k V := Module.Finite.span_of_finite k (Set.finite_range g)
  let : Finite V := Module.finite_of_finite k
  refine Finite.of_injective (Submodule.inclusion
    (show curveChartAdditiveQuotient k F s ≤ V from ?_)) (Submodule.inclusion_injective _)
  intro x hx
  obtain ⟨d, hd, rfl⟩ := Submodule.mem_map.mp hx
  have hD : d ∈ CurveModel.chartRing k (insert s⁻¹ ({s} : Set F)) := by
    rw [Set.pair_comm]
    exact hd
  obtain ⟨n, hn⟩ := CurveModel.exists_pow_mul_mem_chartRing (K := k)
    (Set.mem_singleton s) hs hD
  let d₀ : B := ⟨s^n * d, hn⟩
  have hBmem : s ∈ B := CurveModel.subset_chartRing k _ (Set.mem_singleton s)
  have hCmem : s⁻¹ ∈ C := CurveModel.subset_chartRing k _ (Set.mem_singleton s⁻¹)
  have hzeroB {y : F} (hy : y ∈ B) : q y = 0 :=
    (Submodule.Quotient.mk_eq_zero W).2 ((show B.toSubmodule ≤ W from le_sup_left) hy)
  have hzeroC {y : F} (hy : y ∈ C) : q y = 0 :=
    (Submodule.Quotient.mk_eq_zero W).2 ((show C.toSubmodule ≤ W from le_sup_right) hy)
  have hmonomial (i) (j : ℕ) : q ((s⁻¹)^n * s^j * (b i : F)) ∈ V := by
    by_cases hj : n ≤ j
    · obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hj
      have heq : (s⁻¹)^n * s^(n+a) = s^a := by
        rw [pow_add, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hs, one_pow, one_mul]
      rw [heq, hzeroB (B.mul_mem (B.pow_mem hBmem _) (b i).property)]
      exact V.zero_mem
    · have hj' : j ≤ n := by omega
      have heq : (s⁻¹)^n * s^j = (s⁻¹)^(n-j) := by
        conv_lhs => rw [← Nat.sub_add_cancel hj']
        rw [pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ hs, one_pow, mul_one]
      rw [heq]
      by_cases hm' : n-j ≤ m i
      · exact Submodule.subset_span ⟨⟨i, ⟨n-j, by omega⟩⟩, rfl⟩
      · have heq' : n-j = (n-j-m i) + m i := by omega
        rw [heq', pow_add, mul_assoc,
          hzeroC (C.mul_mem (C.pow_mem hCmem _) (hm i))]
        exact V.zero_mem
  have hpoly (i) (p : k[X]) : q ((s⁻¹)^n * (aeval s p : F) * (b i : F)) ∈ V := by
    induction p using Polynomial.induction_on' with
    | add p r hp hr =>
      rw [map_add, mul_add, add_mul, map_add]
      exact V.add_mem hp hr
    | monomial j c =>
      rw [Polynomial.aeval_monomial]
      have heq : (s⁻¹)^n * (algebraMap k F c * s^j) * (b i : F) =
          c • ((s⁻¹)^n * s^j * (b i : F)) := by rw [Algebra.smul_def]; ring
      rw [heq, map_smul]
      exact V.smul_mem c (hmonomial i j)
  have hrepr : ∑ i, (b.repr d₀ i : F) * (b i : F) = (d₀ : F) := by
    calc
      _ = B.val (∑ i, b.repr d₀ i • b i) := by
        rw [map_sum]
        rfl
      _ = (d₀ : F) := congrArg (fun c : B => (c : F)) (b.sum_repr d₀)
  have hdrepr : d = ∑ i, (s⁻¹)^n * (b.repr d₀ i : F) * (b i : F) := by
    simp only [mul_assoc, ← Finset.mul_sum, hrepr]
    change d = (s⁻¹)^n * (s^n * d)
    rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hs, one_pow, one_mul]
  change q d ∈ V
  rw [hdrepr, map_sum]
  apply V.sum_mem
  intro i _
  obtain ⟨p, hp⟩ := CurveModel.aevalAdjoin_surjective k s (b.repr d₀ i)
  rw [← hp]
  exact hpoly _ _

end Langlands.Global
