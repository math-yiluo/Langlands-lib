import Langlands.Global.AdelicRegularizedConeFourierBoundary
import Langlands.Global.ImaginaryAxisLocalDivision
import Langlands.Analysis.Meromorphic.ImaginaryHyperplaneDivision

/-! # Holomorphic identification of a finite regularized orthant sum -/

noncomputable section

open Set Metric

set_option autoImplicit false

namespace Langlands.Global

open ImaginaryAxis Langlands.Analysis.Meromorphic.ImaginaryHyperplane

/-- Equality on a dense subset of the imaginary slice identifies two holomorphic functions
on an open neighborhood of the slice. -/
theorem exists_eqOn_of_dense_imaginarySlice {n : ℕ} {f g : (Fin n → ℂ) → ℂ}
    {U : Set (Fin n → ℂ)} {S : Set (Fin n → ℝ)}
    (hU : IsOpen U) (haxis : range imaginarySlice ⊆ U)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (hS : Dense S) (he : ∀ x ∈ S, f (imaginarySlice x) = g (imaginarySlice x)) :
    ∃ W, IsOpen W ∧ range imaginarySlice ⊆ W ∧ W ⊆ U ∧ EqOn f g W := by
  have hcont {k : (Fin n → ℂ) → ℂ} (hk : DifferentiableOn ℂ k U) :
      Continuous (fun x => k (imaginarySlice x)) :=
    continuousOn_univ.mp (hk.continuousOn.comp continuous_imaginarySlice.continuousOn
      (fun x _ => haxis (mem_range_self x)))
  have heq : (fun x => f (imaginarySlice x)) = fun x => g (imaginarySlice x) :=
    (hcont hf).ext_on hS (hcont hg) he
  have hball (x : Fin n → ℝ) :
      ∃ r > 0, ball (imaginarySlice x) r ⊆ U :=
    Metric.isOpen_iff.mp hU _ (haxis (mem_range_self x))
  choose r hr hsub using hball
  refine ⟨⋃ x, ball (imaginarySlice x) (r x), isOpen_iUnion (fun _ => isOpen_ball), ?_,
    iUnion_subset hsub, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact mem_iUnion.mpr ⟨x, mem_ball_self (hr x)⟩
  · intro s hs
    obtain ⟨x, hx⟩ := mem_iUnion.mp hs
    apply sub_eq_zero.mp
    refine eqOn_zero_of_eqOn_imaginary (s₀ := imaginarySlice x)
      (fun j => by simp [imaginarySlice, Complex.mul_re])
      ((hf.sub hg).mono (hsub x)) (fun z _ hz => ?_) s hx
    have hz' : imaginarySlice (fun j => (z j).im) = z := by
      funext j
      apply Complex.ext
      · simp [imaginarySlice, Complex.mul_re, hz j]
      · simp [imaginarySlice, Complex.mul_im]
    rw [← hz']
    exact sub_eq_zero.mpr (congrFun heq _)

private theorem prod_mul_sum_div_eq_sum_prod_erase {I : Type*} [DecidableEq I]
    (t : Finset I) (a d : I → ℂ) (hd : ∀ i ∈ t, d i ≠ 0) :
    (∏ i ∈ t, d i) * (∑ i ∈ t, a i / d i) =
      ∑ i ∈ t, (∏ j ∈ t.erase i, d j) * a i := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← Finset.prod_erase_mul t d hi, mul_assoc]
  congr 1
  rw [mul_comm (d i), div_mul_cancel₀ _ (hd i hi)]

private theorem differentiableOn_finsetProduct {n : ℕ} {I : Type*} [DecidableEq I]
    {U : Set (Fin n → ℂ)} (t : Finset I) {f : I → (Fin n → ℂ) → ℂ}
    (hf : ∀ i ∈ t, DifferentiableOn ℂ (f i) U) :
    DifferentiableOn ℂ (fun s => ∏ i ∈ t, f i s) U := by
  intro s hs
  exact (HasFDerivWithinAt.finsetProd
    (fun i hi => (hf i hi s hs).hasFDerivWithinAt)).differentiableWithinAt

/-- A finite sum of regularized orthant terms with fixed polynomial symbols and holomorphic
weights agrees with its holomorphic representative near the imaginary slice wherever
all the coroot denominators are nonzero. -/
def FiniteOrthantHolomorphicIdentificationStatement : Prop :=
  ∀ {n : ℕ} {L : Type*} [Fintype L] {ι : L → Type*} [∀ l, Fintype (ι l)]
    (b : ∀ l, ι l → ℝ) (P : ∀ l, MvPolynomial (ι l) ℂ)
    (z : ∀ l, (Fin n → ℂ) → ι l → ℂ) (a : L → (Fin n → ℂ) → ℂ)
    (ω : (Fin n → ℂ) → ℂ) (U : Set (Fin n → ℂ)) (S : Set (Fin n → ℝ)),
    IsOpen U → range imaginarySlice ⊆ U → Dense S →
    DifferentiableOn ℂ ω U →
    (∀ l, DifferentiableOn ℂ (a l) U) →
    (∀ l i, DifferentiableOn ℂ (fun s => z l s i) U) →
    (∀ x ∈ S, (∀ l i, z l (imaginarySlice x) i ≠ 0) ∧
      ω (imaginarySlice x) =
        ∑ l, a l (imaginarySlice x) * regularizedOrthantTerm (b l) (P l) (z l (imaginarySlice x))) →
    ∃ W, IsOpen W ∧ range imaginarySlice ⊆ W ∧ W ⊆ U ∧
      ∀ s ∈ W, (∀ l i, z l s i ≠ 0) →
        ω s = ∑ l, a l s * regularizedOrthantTerm (b l) (P l) (z l s)

/-- Use the finite monomial expansion to clear the denominators before applying the
imaginary-slice identity theorem. -/
theorem finiteOrthantHolomorphicIdentification : FiniteOrthantHolomorphicIdentificationStatement := by
  classical
  intro n L _ ι _ b P z a ω U S hU haxis hS hω ha hz hmatch
  let Q (l : L) := polynomialShift (b l) (P l)
  let J := Σ l : L, {m // m ∈ (Q l).support}
  let denominator (l : L) (m : ι l →₀ ℕ) (s : Fin n → ℂ) := ∏ i, z l s i ^ (m i + 1)
  let numerator (l : L) (m : ι l →₀ ℕ) (s : Fin n → ℂ) :=
    (a l s * Complex.exp (∑ i, (b l i : ℂ) * z l s i) * (Q l).coeff m) *
      ∏ i, (-1 : ℂ) ^ (m i) * ((m i).factorial : ℂ)
  let d (j : J) := denominator j.1 j.2.val
  let c (j : J) := numerator j.1 j.2.val
  let D (s : Fin n → ℂ) := ∏ j, d j s
  let N (s : Fin n → ℂ) := ∑ j : J, (∏ k ∈ Finset.univ.erase j, d k s) * c j s
  have hd (j : J) : DifferentiableOn ℂ (d j) U :=
    differentiableOn_finsetProduct Finset.univ (fun i _ => (hz j.1 i).pow _)
  have hc (j : J) : DifferentiableOn ℂ (c j) U := by
    refine (((ha j.1).mul (DifferentiableOn.cexp ?_)).mul_const _).mul_const _
    apply DifferentiableOn.fun_sum
    exact fun i _ => (hz j.1 i).const_mul _
  have hD : DifferentiableOn ℂ D U :=
    differentiableOn_finsetProduct Finset.univ (fun j _ => hd j)
  have hN : DifferentiableOn ℂ N U :=
    DifferentiableOn.fun_sum fun j _ =>
      (differentiableOn_finsetProduct (Finset.univ.erase j) (fun k _ => hd k)).mul (hc j)
  have hform (s : Fin n → ℂ) :
      (∑ l, a l s * regularizedOrthantTerm (b l) (P l) (z l s)) =
        ∑ j : J, c j s / d j s := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun l _ => ?_
    change _ = ∑ m : (Q l).support, numerator l m s / denominator l m s
    rw [Finset.sum_coe_sort _ (fun m => numerator l m s / denominator l m s)]
    simp only [regularizedOrthantTerm, negativeOrthantRegularizedIntegral, Q, numerator, denominator,
      Finset.mul_sum, orthantFactor, Finset.prod_div_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  have hden (s : Fin n → ℂ) (hs : ∀ l i, z l s i ≠ 0) (j : J) : d j s ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hs j.1 i)
  have hclear (s : Fin n → ℂ) (hs : ∀ l i, z l s i ≠ 0) :
      D s * (∑ l, a l s * regularizedOrthantTerm (b l) (P l) (z l s)) = N s := by
    rw [hform]
    exact prod_mul_sum_div_eq_sum_prod_erase Finset.univ _ _ (fun j _ => hden s hs j)
  obtain ⟨W, hW, hWaxis, hWU, he⟩ :=
    exists_eqOn_of_dense_imaginarySlice hU haxis (hD.mul hω) hN hS
      (fun x hx => (congrArg (D (imaginarySlice x) * ·) (hmatch x hx).2).trans
        (hclear _ (hmatch x hx).1))
  refine ⟨W, hW, hWaxis, hWU, fun s hs hz₀ => ?_⟩
  exact mul_left_cancel₀ (Finset.prod_ne_zero_iff.mpr fun j _ => hden s hz₀ j)
    ((he hs).trans (hclear s hz₀).symm)

end Langlands.Global
