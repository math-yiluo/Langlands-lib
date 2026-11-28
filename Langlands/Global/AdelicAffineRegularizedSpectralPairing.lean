import Langlands.Global.AdelicTruncationAffineDenominators

/-! # Affine denominators of a finite regularized spectral pairing -/

noncomputable section

open Set Langlands.Analysis.Meromorphic

set_option autoImplicit false

namespace Langlands.Global.ImaginaryAxis

variable {n : ℕ} {I : Type*} [Fintype I] {σ : I → Type*} [∀ i, Fintype (σ i)]

local notation "Spectral" => (Fin n → ℂ)

/-- Finite sum of regularized orthant integrals with an exponential prefactor for each
translated cone and a holomorphic spectral coefficient for each indexed polynomial. -/
def affineRegularizedSum
    (a : ∀ i, σ i → Spectral → ℂ) (c : I → Spectral → ℂ)
    (t : ∀ i, σ i → ℝ) (p : ∀ i, MvPolynomial (σ i) ℂ) (s : Spectral) : ℂ :=
  ∑ i, c i s *
    (Complex.exp (∑ α, (t i α : ℂ) * a i α s) *
      negativeOrthantRegularizedIntegral (fun α => a i α s) (polynomialShift (t i) (p i)))

private def clearedOrthant {J : Type*} [Fintype J] (a : J → ℂ) (q : MvPolynomial J ℂ) : ℂ :=
  ∑ k ∈ q.support, q.coeff k *
    ∏ α, ((-1 : ℂ) ^ k α * (k α).factorial) * a α ^ (q.degreeOf α + 1 - (k α + 1))

private theorem clearedOrthant_eq {J : Type*} [Fintype J] (a : J → ℂ) (q : MvPolynomial J ℂ)
    (ha : ∀ α, a α ≠ 0) :
    clearedOrthant a q = (∏ α, a α ^ (q.degreeOf α + 1)) * negativeOrthantRegularizedIntegral a q := by
  unfold clearedOrthant negativeOrthantRegularizedIntegral
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [mul_left_comm, ← Finset.prod_mul_distrib]
  apply congrArg (q.coeff k * ·)
  refine Finset.prod_congr rfl fun α _ => ?_
  rw [orthantFactor, pow_sub₀ _ (ha α) (Nat.add_le_add_right (q.le_degreeOf_of_mem_support α hk) 1), div_eq_mul_inv]
  ac_rfl

private theorem differentiable_clearedOrthant {J : Type*} [Fintype J] {a : J → Spectral → ℂ}
    (ha : ∀ α, Differentiable ℂ (a α)) (q : MvPolynomial J ℂ) :
    Differentiable ℂ (fun s => clearedOrthant (fun α => a α s) q) := by
  unfold clearedOrthant
  refine Differentiable.fun_sum fun k _ => Differentiable.const_mul ?_ _
  exact differentiable_finsetProd_apply Finset.univ fun α _ =>
    ((ha α).pow (q.degreeOf α + 1 - (k α + 1))).const_mul _

/-- For affine coroot values real on real inputs in their linear parts, the regularized
finite sum has the local hyperplane presentation at every point of the imaginary slice.
Its holomorphy away from these hyperplanes is asserted on the common coefficient domain. -/
def AffineRegularizedSumPresentationStatement : Prop :=
  ∀ (l : ∀ i, σ i → Spectral →ₗ[ℂ] ℂ) (b : ∀ i, σ i → ℂ)
    (c : I → Spectral → ℂ) (t : ∀ i, σ i → ℝ) (p : ∀ i, MvPolynomial (σ i) ℂ)
    (U : Set Spectral),
    let a (i : I) (α : σ i) (s : Spectral) := l i α s + b i α
    let D := {s | ∀ i α, a i α s ≠ 0}
    let f := affineRegularizedSum a c t p
    IsOpen U → Set.range (imaginarySlice (n := n)) ⊆ U → (∀ i, DifferentiableOn ℂ (c i) U) →
    (∀ i α (x : Fin n → ℝ), (l i α (fun j => (x j : ℂ))).im = 0) →
    (∀ i α, ∃ x : Fin n → ℝ, a i α (imaginarySlice x) ≠ 0) →
    DifferentiableOn ℂ f (U ∩ D) ∧ HasImaginaryHyperplanePresentation f (U ∩ D)

set_option maxHeartbeats 1400000 in
/-- Clear every monomial denominator using the degree in each translated polynomial
variable, then multiply by the other summands' factors to obtain a common numerator. -/
theorem affineRegularizedSumPresentation : AffineRegularizedSumPresentationStatement (n := n) (σ := σ) := by
  classical
  intro l b c t p U a D f hU hI hc hreal hnonzero
  let q (i : I) := polynomialShift (t i) (p i)
  let N (i : I) (α : σ i) := (q i).degreeOf α + 1
  let m (i : I) (s : Spectral) := ∏ α, a i α s ^ N i α
  let E (i : I) (s : Spectral) := Complex.exp (∑ α, (t i α : ℂ) * a i α s)
  let v (i : I) (s : Spectral) := c i s * (E i s * clearedOrthant (fun α => a i α s) (q i))
  let h (s : Spectral) := ∑ i, (∏ j ∈ Finset.univ.erase i, m j s) * v i s
  have ha (i : I) (α : σ i) : Differentiable ℂ (a i α) :=
    (l i α).toContinuousLinearMap.differentiable.add_const _
  have hm (i : I) : Differentiable ℂ (m i) := by
    change Differentiable ℂ (fun s : Spectral => ∏ α : σ i, (a i α s) ^ N i α)
    exact differentiable_finsetProd_apply Finset.univ fun α _ => (ha i α).pow _
  have hE (i : I) : Differentiable ℂ (E i) := by
    change Differentiable ℂ (fun s : Spectral => Complex.exp (∑ α : σ i, (t i α : ℂ) * a i α s))
    exact (Differentiable.fun_sum fun α _ => (ha i α).const_mul _).cexp
  have hv (i : I) : DifferentiableOn ℂ (v i) U :=
    (hc i).mul ((hE i).mul (differentiable_clearedOrthant (ha i) (q i))).differentiableOn
  have hh : DifferentiableOn ℂ h U := by
    dsimp only [h]
    exact DifferentiableOn.fun_sum fun i _ =>
      (differentiable_finsetProd_apply (Finset.univ.erase i) fun j _ => hm j).differentiableOn.mul (hv i)
  have hnum (s : Spectral) (hs : s ∈ D) : h s = (∏ i, m i s) * f s := by
    have hz (i : I) : clearedOrthant (fun α => a i α s) (q i) = m i s *
        negativeOrthantRegularizedIntegral (fun α => a i α s) (q i) :=
      clearedOrthant_eq _ _ (hs i)
    change (∑ i, (∏ j ∈ Finset.univ.erase i, m j s) * v i s) = _ * affineRegularizedSum a c t p s
    rw [affineRegularizedSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    dsimp only [v]
    rw [hz i, ← Finset.prod_erase_mul Finset.univ (fun j => m j s) hi]
    change _ = _ * (c i s * (E i s * negativeOrthantRegularizedIntegral (fun α => a i α s) (q i)))
    ring
  have hd (s : Spectral) (hs : s ∈ D) : (∏ i, m i s) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ =>
      Finset.prod_ne_zero_iff.mpr fun α _ => pow_ne_zero _ (hs i α)
  have hdiff : DifferentiableOn ℂ f (U ∩ D) := by
    have hi : DifferentiableOn ℂ (fun s => (∏ i, m i s)⁻¹) (U ∩ D) :=
      (differentiable_finsetProd_apply Finset.univ fun i _ => hm i).differentiableOn.inv
        (fun s hs => hd s hs.2)
    refine ((hh.mono inter_subset_left).mul hi).congr ?_
    intro s hs
    have he : f s = h s / (∏ i, m i s) :=
      (eq_div_iff (hd s hs.2)).2 ((mul_comm _ _).trans (hnum s hs.2).symm)
    simpa only [div_eq_mul_inv, Pi.mul_apply] using he
  let J := Σ i : I, Σ α : σ i, Fin (N i α)
  let l' (j : J) := l j.1 j.2.1
  let b' (j : J) := b j.1 j.2.1
  have hp (s : Spectral) : (∏ j : J, (l' j s + b' j)) = ∏ i, m i s := by
    simp only [J, Fintype.prod_sigma, l', b', Finset.prod_const, Finset.card_univ, Fintype.card_fin, m, a]
  refine ⟨hdiff, hasImaginaryHyperplanePresentation_of_affine_product l' b'
    (fun j => hreal j.1 j.2.1) (fun j => hnonzero j.1 j.2.1) hU hI hh ?_⟩
  intro s hs
  change h s = (∏ j : J, (l' j s + b' j)) * f s
  rw [hp, hnum s hs.2.2]

end Langlands.Global.ImaginaryAxis
