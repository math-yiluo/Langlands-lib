import Langlands.Representation.Archimedean.RealInductionStagesFamily
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! # Pointwise analytic families in finite-dimensional ranges -/

noncomputable section

open Filter Set
open scoped Topology Matrix

set_option autoImplicit false

namespace Langlands.Analysis

private theorem differentiable_det {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Fintype ι] [DecidableEq ι] (A : E → Matrix ι ι ℂ) (hA : ∀ i j, Differentiable ℂ (fun z => A z i j)) :
    Differentiable ℂ (fun z => (A z).det) := by
  simp only [Matrix.det_apply]
  apply Differentiable.fun_sum
  intro π _
  have hprod (S : Finset ι) : Differentiable ℂ (fun z => ∏ i ∈ S, A z (π i) i) := by
    induction S using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty] using (differentiable_const (1 : ℂ))
    | insert i S hi hS =>
        simpa only [Finset.prod_insert hi] using (hA (π i) i).fun_mul hS
  exact (hprod Finset.univ).const_smul _

/-- Suppose a set of parameters determines entire scalar functions uniquely. A pointwise entire
family lying in the range of a finite-dimensional analytic family of linear maps on this set
lies in the range at every parameter where the map is injective. -/
theorem mem_range_of_pointwise_analytic_on {E X V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (T : E → V →ₗ[ℂ] (X → ℂ))
    (W : E → X → ℂ) (S : Set E)
    (hS : ∀ f : E → ℂ, Differentiable ℂ f → (∀ z ∈ S, f z = 0) → f = 0)
    (hT : ∀ v x, Differentiable ℂ (fun z => T z v x)) (hW : ∀ x, Differentiable ℂ (W · x))
    {z₀ : E} (h₀ : Function.Injective (T z₀)) (h₁ : ∀ z ∈ S, W z ∈ LinearMap.range (T z)) :
    W z₀ ∈ LinearMap.range (T z₀) := by
  classical
  let I := Fin (Module.finrank ℂ V)
  let b : Module.Basis I ℂ V := Module.finBasis ℂ V
  let H := LinearMap.range (T z₀)
  let e : V ≃ₗ[ℂ] H := LinearEquiv.ofInjective (T z₀) h₀
  let : FiniteDimensional ℂ H := e.finiteDimensional
  choose m p c h using fun i : I =>
    Langlands.Archimedean.InductionStages.exists_eval_sum H ((b.coord i).comp e.symm.toLinearMap)
  let L (i : I) (f : X → ℂ) : ℂ := ∑ j : Fin (m i), c i j * f (p i j)
  have hL (v : V) (i : I) : L i (T z₀ v) = b.coord i v := by
    have ha := (h i (e v)).symm
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at ha
    exact ha
  let A (z : E) : Matrix I I ℂ := Matrix.of fun i j => L i (T z (b j))
  let u (z : E) (i : I) := L i (W z)
  have hA (i j : I) : Differentiable ℂ (fun z => A z i j) := by
    change Differentiable ℂ (fun z => ∑ l : Fin (m i), c i l * T z (b j) (p i l))
    exact Differentiable.fun_sum fun l _ => (hT (b j) (p i l)).const_mul (c i l)
  have hu (i : I) : Differentiable ℂ (fun z => u z i) :=
    Differentiable.fun_sum fun l _ => (hW (p i l)).const_mul (c i l)
  have hA₀ : A z₀ = 1 := by
    ext i j
    change L i (T z₀ (b j)) = _
    rw [hL, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, Matrix.one_apply]
    split_ifs <;> simp_all
  have hAd (i j : I) : Differentiable ℂ (fun z => (A z).adjugate i j) := by
    simp only [Matrix.adjugate_apply]
    apply differentiable_det
    intro a k
    by_cases ha : a = j
    · subst a
      simp only [Matrix.updateRow_self]
      exact differentiable_const _
    · simpa only [Matrix.updateRow_ne ha] using hA a k
  let v (z : E) : V := ∑ i : I, ((A z).adjugate *ᵥ u z) i • b i
  have hTd (x : X) : Differentiable ℂ (fun z => T z (v z) x) := by
    simp only [v, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Differentiable.fun_sum
    intro i _
    refine (Differentiable.fun_sum fun j _ => (hAd i j).mul (hu j)).mul (hT (b i) x)
  have hUd (x : X) : Differentiable ℂ (fun z => (A z).det * W z x) :=
    (differentiable_det A hA).mul (hW x)
  have hEq (x : X) : (fun z => (A z).det * W z x - T z (v z) x) = 0 := by
    apply hS _ ((hUd x).sub (hTd x))
    intro z hz
    apply sub_eq_zero.mpr
    change (A z).det * W z x = T z (v z) x
    obtain ⟨q, hq⟩ := h₁ z hz
    have hCoords : u z = A z *ᵥ (fun i => b.repr q i) := by
      funext i
      change L i (W z) = ∑ j : I, A z i j * b.repr q j
      rw [← hq]
      nth_rewrite 1 [← b.sum_repr q]
      rw [map_sum]
      simp only [map_smul, L, Finset.sum_apply, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [A, Matrix.of_apply]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l _
      ring
    have hv : v z = (A z).det • q := by
      dsimp only [v]
      rw [hCoords, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
      simp_rw [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, b.sum_repr]
    rw [hv, map_smul, Pi.smul_apply, smul_eq_mul, hq]
  refine ⟨v z₀, funext fun x => ?_⟩
  have h := sub_eq_zero.mp (congrFun (hEq x) z₀)
  simpa only [hA₀, Matrix.det_one, one_mul] using h.symm

end Langlands.Analysis
