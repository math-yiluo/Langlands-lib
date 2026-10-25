import Langlands.Representation.Induction.CompactQuotientProof
import Langlands.Representation.Unitary.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Compact integration of positive forms

A constructor on actual smooth covariant functions. Integrability and scalar
right-translation invariance are explicit inputs; no existence theorem for
such a scalar functional is asserted.
-/

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace Langlands.Induction

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (P : Subgroup G) (τ : Representation ℂ P V)

/-- Any algebraic core pairing of two smooth induced functions is locally constant. -/
theorem pairing_isLocallyConstant (b : InnerProductSpace.Core ℂ V)
    (f h : SmoothFunctions P τ) :
    IsLocallyConstant (fun x => b.inner (eval P τ f x) (eval P τ h x)) :=
  (eval_isLocallyConstant P τ f).comp₂ (eval_isLocallyConstant P τ h) b.inner

/-- Integrate a positive form on the actual covariant function space. Full support
and `G = P K` give definiteness; the separate scalar identity gives invariance. -/
def integralInvariantPositiveForm
    (b : InnerProductSpace.Core ℂ V) (K : Subgroup G)
    [MeasurableSpace K] (μ : Measure K) [μ.IsOpenPosMeasure]
    (hPK : ∀ g : G, ∃ (q : P) (k : K), g = (q : G) * (k : G))
    (hint : ∀ f h : SmoothFunctions P τ,
      Integrable (fun k : K => b.inner (eval P τ f k) (eval P τ h k)) μ)
    (hinv : ∀ (g : G) (f h : SmoothFunctions P τ),
      (∫ k : K, b.inner (eval P τ f ((k : G) * g))
        (eval P τ h ((k : G) * g)) ∂μ) =
      ∫ k : K, b.inner (eval P τ f k) (eval P τ h k) ∂μ) :
    InvariantPositiveForm (smoothInduced P τ) where
  inner f h := ∫ k : K, b.inner (eval P τ f k) (eval P τ h k) ∂μ
  conj_inner_symm f h := by
    rw [← integral_conj]
    exact integral_congr_ae (Filter.Eventually.of_forall fun k =>
      b.conj_inner_symm (eval P τ f k) (eval P τ h k))
  re_inner_nonneg f := by
    rw [← integral_re (hint f f)]
    exact integral_nonneg fun k => b.re_inner_nonneg (eval P τ f k)
  add_left f h j := by
    change (∫ k : K, b.inner (eval P τ f k + eval P τ h k) (eval P τ j k) ∂μ) = _
    simp_rw [b.add_left]
    exact integral_add (hint f j) (hint h j)
  smul_left f h c := by
    change (∫ k : K, b.inner (c • eval P τ f k) (eval P τ h k) ∂μ) = _
    simp_rw [b.smul_left]
    exact integral_const_mul _ _
  definite f hf := by
    let : InnerProductSpace.Core ℂ V := b
    have hzero : (∫ k : K, (b.inner (eval P τ f k) (eval P τ f k)).re ∂μ) = 0 := by
      change (∫ k : K, RCLike.re (b.inner (eval P τ f k) (eval P τ f k)) ∂μ) = 0
      rw [integral_re (hint f f), hf]
      rfl
    have hae : (fun k : K => (b.inner (eval P τ f k) (eval P τ f k)).re) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg
        (fun k : K => b.re_inner_nonneg (eval P τ f k)) (hint f f).re).mp hzero
    have hcont : Continuous
        (fun k : K => (b.inner (eval P τ f k) (eval P τ f k)).re) :=
      ((pairing_isLocallyConstant P τ b f f).comp Complex.re).continuous.comp
        continuous_subtype_val
    have heq := Measure.eq_of_ae_eq hae hcont continuous_const
    have hkzero (k : K) : eval P τ f k = 0 := by
      apply (InnerProductSpace.Core.normSq_eq_zero (𝕜 := ℂ)).mp
      exact congrFun heq k
    apply Subtype.ext
    apply Subtype.ext
    funext g
    obtain ⟨q, k, rfl⟩ := hPK g
    change eval P τ f ((q : G) * (k : G)) = 0
    rw [show eval P τ f ((q : G) * (k : G)) = τ q (eval P τ f k) from f.1.2 q k,
      hkzero, map_zero]
  invariant g f h := hinv g f h

end Langlands.Induction
