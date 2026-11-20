import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! # Continuation of linear functionals from holomorphic spanning families -/

noncomputable section

open Filter Set Matrix
open scoped Matrix Topology Classical

set_option autoImplicit false

namespace Langlands.Analysis

variable {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {n : ℕ}
local notation "V" => Fin n → ℂ
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

private theorem eq_of_differentiable_eqOn_open {f g : E → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) {S : Set E} (hS : IsOpen S) (hne : S.Nonempty) (hfg : EqOn f g S) : f = g := by
  obtain ⟨q, hq⟩ := hne
  funext p
  let L (z : ℂ) := q + z • (p - q)
  have hL : Differentiable ℂ L := (differentiable_id.smul_const (p - q)).const_add q
  have hLzero : L 0 = q := by simp [L]
  have hLone : L 1 = p := by simp [L, add_comm q]
  have hmem : ∀ᶠ z in 𝓝 (0 : ℂ), L z ∈ S := by
    apply hL.continuous.continuousAt.preimage_mem_nhds
    rw [hLzero]
    exact hS.mem_nhds hq
  have heq : (f ∘ L) =ᶠ[𝓝 (0 : ℂ)] (g ∘ L) := hmem.mono fun z hz => hfg hz
  have h := AnalyticOnNhd.eq_of_eventuallyEq
    (fun z _ => (hf.comp hL).analyticAt z) (fun z _ => (hg.comp hL).analyticAt z) heq
  simpa only [Function.comp_apply, hLone] using congrFun h 1

private theorem differentiable_det {A : E → Mat}
    (hA : ∀ i j, Differentiable ℂ (fun q => A q i j)) : Differentiable ℂ (fun q => (A q).det) := by
  simp only [Matrix.det_apply']
  apply Differentiable.fun_sum
  intro e _
  have hprod (I : Finset (Fin n)) : Differentiable ℂ (fun q => ∏ i ∈ I, A q (e i) i) := by
    induction I using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty] using differentiable_const (1 : ℂ)
    | insert i I hi ih =>
      simp only [Finset.prod_insert hi]
      exact (hA (e i) i).mul ih
  exact (hprod Finset.univ).const_mul _

private theorem differentiable_cramer {A : E → Mat} {y : E → V}
    (hA : ∀ i j, Differentiable ℂ (fun q => A q i j)) (hy : ∀ i, Differentiable ℂ (fun q => y q i))
    (i : Fin n) : Differentiable ℂ (fun q => (A q).cramer (y q) i) := by
  simp only [Matrix.cramer_apply]
  apply differentiable_det
  intro j k
  by_cases hk : k = i
  · simpa [hk] using hy j
  · simpa [Matrix.updateCol_ne, hk] using hA j k

private theorem cramer_mulVec (A : Mat) (x : V) : A.cramer (A *ᵥ x) = A.det • x := by
  rw [Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
    Matrix.smul_mulVec, Matrix.one_mulVec]

private theorem cramer_div_eq (A : Mat) (x y : V) (hA : A.det ≠ 0) (h : A *ᵥ x = y) (i : Fin n) :
    A.cramer y i / A.det = x i := by
  rw [← h, cramer_mulVec, Pi.smul_apply, smul_eq_mul, mul_comm A.det, mul_div_cancel_right₀ _ hA]

private def frame (v : J → E → V) (b : Fin n → J) (q : E) : Mat := fun i j => v (b i) q j

/-- Compatible scalar values on a holomorphic spanning family determine a holomorphic family
of linear functionals as soon as the values come from linear functionals on one nonempty open set. -/
def HolomorphicLinearContinuationStatement (E J : Type*) (n : ℕ)
    [NormedAddCommGroup E] [NormedSpace ℂ E] : Prop :=
  ∀ (v : J → E → Fin n → ℂ) (F : J → E → ℂ),
    (∀ j i, Differentiable ℂ (fun q => v j q i)) → (∀ j, Differentiable ℂ (F j)) →
    (∀ q, ∃ b : Fin n → J, (frame v b q).det ≠ 0) →
    ∀ (S : Set E), IsOpen S → S.Nonempty → ∀ c₀ : E → Fin n → ℂ,
      (∀ q ∈ S, ∀ j, v j q ⬝ᵥ c₀ q = F j q) →
      ∃ c : E → Fin n → ℂ,
        (∀ i, Differentiable ℂ (fun q => c q i)) ∧
        (∀ q j, v j q ⬝ᵥ c q = F j q) ∧ Set.EqOn c c₀ S

theorem holomorphicLinearContinuation : HolomorphicLinearContinuationStatement E J n := by
  intro v F hv hF hsp S hS hne c₀ hc₀
  choose b hb using hsp
  let y (a : Fin n → J) (q : E) : V := fun i => F (a i) q
  have hdet (a : Fin n → J) : Differentiable ℂ (fun q => (frame v a q).det) :=
    differentiable_det fun i j => hv (a i) j
  have hnum (a : Fin n → J) (i : Fin n) : Differentiable ℂ (fun q => (frame v a q).cramer (y a q) i) :=
    differentiable_cramer (fun j k => hv (a j) k) (fun j => hF (a j)) i
  have hcross (a : Fin n → J) (j : J) (q : E) :
      v j q ⬝ᵥ (frame v a q).cramer (y a q) = (frame v a q).det * F j q := by
    let f (p : E) : ℂ := v j p ⬝ᵥ (frame v a p).cramer (y a p)
    let g (p : E) : ℂ := (frame v a p).det * F j p
    have hf : Differentiable ℂ f := Differentiable.fun_sum fun i _ => (hv j i).mul (hnum a i)
    have hg : Differentiable ℂ g := (hdet a).mul (hF j)
    apply congrFun (eq_of_differentiable_eqOn_open hf hg hS hne ?_) q
    intro p hp
    have hA : frame v a p *ᵥ c₀ p = y a p := by
      funext i
      exact hc₀ p hp (a i)
    change v j p ⬝ᵥ (frame v a p).cramer (y a p) = _
    rw [← hA, cramer_mulVec, dotProduct_smul, smul_eq_mul, hc₀ p hp]
  let c (q : E) : V := ((frame v (b q) q).det)⁻¹ • (frame v (b q) q).cramer (y (b q) q)
  have hc (q : E) (j : J) : v j q ⬝ᵥ c q = F j q := by
    change v j q ⬝ᵥ (((frame v (b q) q).det)⁻¹ • (frame v (b q) q).cramer (y (b q) q)) = F j q
    rw [dotProduct_smul, smul_eq_mul, hcross, ← mul_assoc, inv_mul_cancel₀ (hb q), one_mul]
  have hA (a : Fin n → J) (q : E) : frame v a q *ᵥ c q = y a q := by
    funext i
    exact hc q (a i)
  refine ⟨c, fun i q => ?_, hc, fun q hq => ?_⟩
  · let a := b q
    let D : Set E := {p | (frame v a p).det ≠ 0}
    have hD : IsOpen D := isOpen_ne_fun (hdet a).continuous continuous_const
    have hq : q ∈ D := hb q
    have hqdiv : DifferentiableAt ℂ
        (fun p : E => (frame v a p).cramer (y a p) i / (frame v a p).det) q := by
      simp only [div_eq_mul_inv]
      change DifferentiableAt ℂ
        ((fun p => (frame v a p).cramer (y a p) i) * (fun p => (frame v a p).det)⁻¹) q
      exact (hnum a i q).mul ((hdet a q).inv hq)
    refine hqdiv.congr_of_eventuallyEq ?_
    have hEv : ∀ᶠ p in 𝓝 q, p ∈ D := hD.mem_nhds hq
    filter_upwards [hEv] with p hp
    exact (cramer_div_eq (frame v a p) (c p) (y a p) hp (hA a p) i).symm
  · funext i
    have hA₀ : frame v (b q) q *ᵥ c₀ q = y (b q) q := by
      funext j
      exact hc₀ q hq (b q j)
    exact (cramer_div_eq _ _ _ (hb q) (hA (b q) q) i).symm.trans
      (cramer_div_eq _ _ _ (hb q) hA₀ i)

end Langlands.Analysis
