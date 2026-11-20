import Langlands.Automorphic.GroupSchemeUniformGrowthCompare
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Pi
import Mathlib.Topology.Baire.Lemmas

/-! # Common local normalization for finitely many continued sections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Langlands.Global.EisensteinJet

open Langlands.Automorphic.GroupSchemeFunctions
open UniformGrowthFrechetSpace

/-- Combine numerators with the complementary factors of their product denominator. -/
def commonNumerator {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (a : Fin n → ℂ) (h : Fin n → V) : (Fin n → ℂ) →ₗ[ℂ] V :=
  LinearMap.lsum ℂ (fun _ : Fin n => ℂ) ℂ fun j =>
    (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight ((∏ l ∈ Finset.univ.erase j, a l) • h j)

@[simp]
theorem commonNumerator_apply {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (a : Fin n → ℂ) (h : Fin n → V) (c : Fin n → ℂ) :
    commonNumerator a h c = ∑ j, c j • (∏ l ∈ Finset.univ.erase j, a l) • h j := by
  simp [commonNumerator]

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {N d : ℕ} (rho : Langlands.GroupScheme.MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (hN : 0 < N) (hrho : Langlands.GroupScheme.IsClosedSubgroup rho)

local notation "Growth[" R "," L "]" =>
  UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L

/-- A finite collection of local holomorphic numerator presentations can use
one denominator, one open finite level, and one uniform moderate growth exponent.
The common presentation acts linearly on the space of coefficient vectors. -/
theorem exists_common_normalization {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {n : ℕ} (z : E) (W U : Fin n → Set E)
    (hW : ∀ j, IsOpen (W j)) (hz : ∀ j, z ∈ W j)
    (hU : ∀ j, IsOpen (U j)) (hUd : ∀ j, W j ⊆ closure (U j))
    (a : Fin n → E → ℂ) (ha : ∀ j, DifferentiableOn ℂ (a j) (W j))
    (hane : ∀ j t, t ∈ U j → a j t ≠ 0)
    (R : Fin n → ℝ) (L : Fin n → Subgroup (FiniteAdelicGroupPoints F G))
    (hL : ∀ j, IsOpen (L j : Set (FiniteAdelicGroupPoints F G)))
    (f : Fin n → E → AdelicGroupPoints F G → ℂ)
    (H : ∀ j, E → Growth[R j, L j])
    (hH : ∀ j (test : Growth[R j, L j] →L[ℂ] ℂ),
      DifferentiableOn ℂ (fun t => test (H j t)) (W j))
    (hEq : ∀ j t, t ∈ W j ∩ U j →
      toFun F G rho hsmooth hcalc hN hrho (R j) (L j) (H j t) = a j t • f j t) :
    ∃ r > 0, ∃ (S : ℝ) (M : Subgroup (FiniteAdelicGroupPoints F G)),
      IsOpen (M : Set (FiniteAdelicGroupPoints F G)) ∧
      ∃ (A : E → ℂ) (J : E → (Fin n → ℂ) →ₗ[ℂ] Growth[S, M]) (V : Set E),
        DifferentiableOn ℂ A (Metric.ball z r) ∧
        (∀ c (test : Growth[S, M] →L[ℂ] ℂ),
          DifferentiableOn ℂ (fun t => test (J t c)) (Metric.ball z r)) ∧
        IsOpen V ∧ V ⊆ Metric.ball z r ∧ Metric.ball z r ⊆ closure V ∧
        (∀ t ∈ V, (∀ j, t ∈ U j) ∧ A t ≠ 0 ∧
          ∀ c, toFun F G rho hsmooth hcalc hN hrho S M (J t c) =
            A t • ∑ j, c j • f j t) := by
  classical
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (isOpen_iInter_of_finite hW) z (Set.mem_iInter.mpr hz)
  let B := Metric.ball z r
  have hB (j : Fin n) : B ⊆ W j := hball.trans (Set.iInter_subset W j)
  obtain ⟨S, hS⟩ := (Set.finite_range R).bddAbove
  let M := ⨅ j, L j
  have hMo : IsOpen (M : Set (FiniteAdelicGroupPoints F G)) := by
    simpa only [M, Subgroup.coe_iInf] using isOpen_iInter_of_finite hL
  let inc (j : Fin n) : Growth[R j, L j] →L[ℂ] Growth[S, M] :=
    weakenCLM F G rho hsmooth hcalc hN hrho (hS (Set.mem_range_self j)) (iInf_le L j)
  let e (j : Fin n) (t : E) := ∏ l ∈ Finset.univ.erase j, a l t
  let A (t : E) := ∏ j, a j t
  let J (t : E) : (Fin n → ℂ) →ₗ[ℂ] Growth[S, M] :=
    commonNumerator (a · t) (fun j => inc j (H j t))
  have hJ (t : E) (c : Fin n → ℂ) :
      J t c = ∑ j, c j • e j t • inc j (H j t) := commonNumerator_apply _ _ _
  let V := B ∩ ⋂ j, U j
  have hV : IsOpen V := Metric.isOpen_ball.inter (isOpen_iInter_of_finite hU)
  have hUV : B ⊆ closure V := by
    let S₀ (j : Fin n) : Set B := Subtype.val ⁻¹' U j
    have hopen := (Metric.isOpen_ball (x := z) (ε := r)).isOpenEmbedding_subtypeVal.isOpenMap
    have hS₀ (j : Fin n) : Dense (S₀ j) :=
      fun x => hopen.preimage_closure_subset_closure_preimage (hUd j (hB j x.property))
    have hD : Dense (⋂ j, S₀ j) := by
      rw [← Set.sInter_range]
      refine (Set.finite_range S₀).dense_sInter ?_ ?_
      · rintro _ ⟨j, rfl⟩
        exact (hU j).preimage continuous_subtype_val
      · rintro _ ⟨j, rfl⟩
        exact hS₀ j
    intro t ht
    refine map_mem_closure continuous_subtype_val (hD ⟨t, ht⟩) ?_
    intro x hx
    exact ⟨x.property, Set.mem_iInter.mpr fun j => Set.mem_iInter.mp hx j⟩
  have hProdDiff (T : Finset (Fin n)) : DifferentiableOn ℂ (fun t => ∏ j ∈ T, a j t) B := by
    intro t ht
    exact (HasFDerivWithinAt.finsetProd (u := T) (g := a) fun j _ =>
      ((ha j).mono (hB j) t ht).hasFDerivWithinAt).differentiableWithinAt
  refine ⟨r, hr, S, M, hMo, A, J, V, ?_, ?_, hV, Set.inter_subset_left, hUV, ?_⟩
  · exact hProdDiff Finset.univ
  · intro c test
    simp only [hJ, map_sum, map_smul, smul_eq_mul]
    apply DifferentiableOn.fun_sum
    intro j _
    exact (differentiableOn_const (c j)).fun_mul ((hProdDiff (Finset.univ.erase j)).fun_mul
      ((hH j (test.comp (inc j))).mono (hB j)))
  · intro t ht
    have htU := Set.mem_iInter.mp ht.2
    refine ⟨htU, Finset.prod_ne_zero_iff.mpr fun j _ => hane j t (htU j), fun c => ?_⟩
    let eval : Growth[S, M] →ₗ[ℂ] (AdelicGroupPoints F G → ℂ) :=
      ⟨⟨toFun F G rho hsmooth hcalc hN hrho S M, fun _ _ => rfl⟩, fun _ _ => rfl⟩
    change eval (J t c) = _
    rw [hJ, map_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [map_smul]
    change c j • e j t •
      toFun F G rho hsmooth hcalc hN hrho S M (inc j (H j t)) = A t • c j • f j t
    rw [show toFun F G rho hsmooth hcalc hN hrho S M (inc j (H j t)) =
        toFun F G rho hsmooth hcalc hN hrho (R j) (L j) (H j t) from rfl,
      hEq j t ⟨hB j ht.1, htU j⟩, smul_smul, smul_smul, smul_smul]
    have hprod : e j t * a j t = A t :=
      Finset.prod_erase_mul Finset.univ (fun l => a l t) (Finset.mem_univ j)
    rw [mul_assoc, hprod, mul_comm (c j)]

end Langlands.Global.EisensteinJet
