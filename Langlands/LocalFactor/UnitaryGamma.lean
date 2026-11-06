import Langlands.LocalFactor.UnitarySpectral
import Langlands.LocalFactor.UnitaryWeilDeligne
import Langlands.LocalFactor.WeilDelignePair

/-! # Orders of spectral gamma expressions for unitary operators -/

noncomputable section

namespace Langlands.LocalFactor

universe uG uV uW

variable {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

/-- Epsilon times the actual reflected Euler reciprocal divided by the original
Euler reciprocal. No factor identity or positive form is part of this definition. -/
def operatorSpectralGamma (A : Module.End ℂ V) (B : Module.End ℂ W)
    (q : ℝ) (hq : 0 < q) (epsilon : ℂ → ℂ) : ℂ → ℂ :=
  fun z => epsilon z * spectralDenominator A q hq z /
    spectralDenominator B q hq (1 - z)

theorem operatorSpectralGamma_meromorphicAt
    (A : Module.End ℂ V) (B : Module.End ℂ W) (q : ℝ) (hq : 0 < q)
    (epsilon : ℂ → ℂ) (s : ℂ) (he : AnalyticAt ℂ epsilon s) :
    MeromorphicAt (operatorSpectralGamma A B q hq epsilon) s := by
  exact (he.mul (analyticAt_spectralDenominator A q hq s)).meromorphicAt.div
    ((analyticAt_spectralDenominator B q hq (1 - s)).comp
      (analyticAt_const.sub analyticAt_id)).meromorphicAt

/-- Reflection preserves order because its derivative is the nonzero scalar -1. -/
theorem spectralReciprocal_reflected_order_nonpos
    (B : Module.End ℂ W) (h : InnerProductSpace.Core ℂ W)
    (hB : ∀ v w, h.inner (B v) (B w) = h.inner v w)
    (q : ℝ) (hq : 1 < q) (s : ℂ) :
    meromorphicOrderAt
      (fun z => (spectralDenominator B q (lt_trans zero_lt_one hq) (1 - z))⁻¹)
      s ≤ 0 := by
  have href :
      meromorphicOrderAt
        ((fun z => (spectralDenominator B q (lt_trans zero_lt_one hq) z)⁻¹) ∘
          (fun z : ℂ => 1 - z)) s =
      meromorphicOrderAt
        (fun z => (spectralDenominator B q (lt_trans zero_lt_one hq) z)⁻¹)
        (1 - s) :=
    meromorphicOrderAt_comp_of_deriv_ne_zero
      (analyticAt_const.sub analyticAt_id) (by simp)
  change meromorphicOrderAt
    ((fun z => (spectralDenominator B q (lt_trans zero_lt_one hq) z)⁻¹) ∘
      (fun z : ℂ => 1 - z)) s ≤ 0
  rw [href]
  exact spectralReciprocal_order_nonpos B h hB q hq (1 - s)

/-- Away from the imaginary axis, the numerator and epsilon are analytic units,
leaving the nonpositive order of the reflected reciprocal. -/
theorem operatorSpectralGamma_order_nonpos
    (A : Module.End ℂ V) (B : Module.End ℂ W)
    (h : InnerProductSpace.Core ℂ V) (k : InnerProductSpace.Core ℂ W)
    (hA : ∀ v w, h.inner (A v) (A w) = h.inner v w)
    (hB : ∀ v w, k.inner (B v) (B w) = k.inner v w)
    (q : ℝ) (hq : 1 < q) (epsilon : ℂ → ℂ) (s : ℂ)
    (he : AnalyticAt ℂ epsilon s) (he0 : epsilon s ≠ 0) (hs : s.re ≠ 0) :
    meromorphicOrderAt
      (operatorSpectralGamma A B q (lt_trans zero_lt_one hq) epsilon) s ≤ 0 := by
  have ha := analyticAt_spectralDenominator A q (lt_trans zero_lt_one hq) s
  have ha0 : spectralDenominator A q (lt_trans zero_lt_one hq) s ≠ 0 :=
    eulerPolynomial_spectral_eval_ne_zero_of_preserves_positive_form A h hA hq hs
  have ho := meromorphicOrderAt_mul_of_ne_zero (he.mul ha) (mul_ne_zero he0 ha0)
    (f := fun z => (spectralDenominator B q (lt_trans zero_lt_one hq) (1 - z))⁻¹)
  change meromorphicOrderAt
    ((fun z => epsilon z * spectralDenominator A q (lt_trans zero_lt_one hq) z) /
      (fun z => spectralDenominator B q (lt_trans zero_lt_one hq) (1 - z))) s ≤ 0
  rw [div_eq_mul_inv]
  change meromorphicOrderAt
    ((epsilon * spectralDenominator A q (lt_trans zero_lt_one hq)) *
      (fun z => (spectralDenominator B q (lt_trans zero_lt_one hq) (1 - z))⁻¹)) s ≤ 0
  rw [ho]
  exact spectralReciprocal_reflected_order_nonpos B k hB q hq s

namespace WeilDeligne

variable {G : Type uG} [Group G] {ν : G →* ℂˣ}

/-- The Euler-polynomial gamma expression for the actual parameter and its dual.
The epsilon function is supplied separately. -/
def spectralGammaExpression (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (I : Subgroup G) [I.Normal] (g : G) (q : ℝ) (hq : 0 < q)
    (epsilon : ℂ → ℂ) : ℂ → ℂ :=
  operatorSpectralGamma (kernelOperator A I g)
    (kernelOperator (WeilDeligneRepresentation.dual A) I g) q hq epsilon

/-- An underlying unitary parameter has no positive gamma order off the
imaginary axis, provided its supplied epsilon is an analytic unit there. -/
theorem spectralGammaExpression_order_nonpos
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (I : Subgroup G) [I.Normal] (hA : A.toFiniteRepresentation.IsUnitary)
    (g : G) (q : ℝ) (hq : 1 < q) (epsilon : ℂ → ℂ) (s : ℂ)
    (he : AnalyticAt ℂ epsilon s) (he0 : epsilon s ≠ 0) (hs : s.re ≠ 0) :
    meromorphicOrderAt
      (spectralGammaExpression A I g q (lt_trans zero_lt_one hq) epsilon) s ≤ 0 := by
  obtain ⟨h, hh⟩ := A.isUnitary_inertiaKernelRepresentation I hA
  have hd : (WeilDeligneRepresentation.dual A).toFiniteRepresentation.IsUnitary :=
    FiniteRepresentation.isUnitary_dual A.toFiniteRepresentation hA
  obtain ⟨k, hk⟩ :=
    (WeilDeligneRepresentation.dual A).isUnitary_inertiaKernelRepresentation I hd
  exact operatorSpectralGamma_order_nonpos (kernelOperator A I g)
    (kernelOperator (WeilDeligneRepresentation.dual A) I g) h k (hh g) (hk g)
    q hq epsilon s he he0 hs

/-- The real-zero restriction required by Appendix pole counting. -/
theorem spectralGammaExpression_real_positive_order_only_zero
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (I : Subgroup G) [I.Normal] (hA : A.toFiniteRepresentation.IsUnitary)
    (g : G) (q : ℝ) (hq : 1 < q) (epsilon : ℂ → ℂ)
    (he : ∀ t : ℝ, AnalyticAt ℂ epsilon (t : ℂ) ∧ epsilon (t : ℂ) ≠ 0)
    (t : ℝ)
    (ht : 0 < meromorphicOrderAt
      (spectralGammaExpression A I g q (lt_trans zero_lt_one hq) epsilon) (t : ℂ)) :
    t = 0 := by
  by_contra ht0
  exact (not_lt_of_ge
    (spectralGammaExpression_order_nonpos A I hA g q hq epsilon t
      (he t).1 (he t).2 (by simpa using ht0))) ht

end WeilDeligne
end Langlands.LocalFactor
