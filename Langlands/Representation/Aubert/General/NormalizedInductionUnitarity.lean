import Langlands.Representation.Induction.CompactIntegralForm
import Langlands.Representation.Induction.CompactQuotientDuality
import Langlands.Representation.Aubert.General.RationalInductionDualityReduction

/-!
# Positive forms on normalized induction from compact quotients

The positive form is defined on the actual smooth covariant functions.
Definiteness uses positivity of the measure near `1` and invariance of every
translated diagonal integral.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ComplexConjugate

namespace Langlands.Induction

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (P : Subgroup G) (τ : Representation ℂ P V)

/-- Integrate a positive form using a measure positive near `1`. Invariance of
all translated diagonal integrals detects every nonzero induced function. -/
def integralInvariantPositiveForm_of_pos
    (b : InnerProductSpace.Core ℂ V) (K : Subgroup G)
    [MeasurableSpace K] (μ : Measure K)
    (hpos : ∀ U : Set K, IsOpen U → (1 : K) ∈ U → 0 < μ U)
    (hpair : ∀ (f h : SmoothFunctions P τ) (g : G),
      Integrable (fun k : K => b.inner (eval P τ f ((k : G) * g))
        (eval P τ h ((k : G) * g))) μ ∧
      (∫ k : K, b.inner (eval P τ f ((k : G) * g))
        (eval P τ h ((k : G) * g)) ∂μ) =
        ∫ k : K, b.inner (eval P τ f k) (eval P τ h k) ∂μ) :
    InvariantPositiveForm (smoothInduced P τ) := by
  have hint (f h : SmoothFunctions P τ) :
      Integrable (fun k : K => b.inner (eval P τ f k) (eval P τ h k)) μ := by
    simpa only [mul_one] using (hpair f h 1).1
  refine
    { inner := fun f h => ∫ k : K, b.inner (eval P τ f k) (eval P τ h k) ∂μ
      conj_inner_symm := ?_
      re_inner_nonneg := ?_
      add_left := ?_
      smul_left := ?_
      definite := ?_
      invariant := ?_ }
  · intro f h
    rw [← integral_conj]
    exact integral_congr_ae (Filter.Eventually.of_forall fun k =>
      b.conj_inner_symm (eval P τ f k) (eval P τ h k))
  · intro f
    rw [← integral_re (hint f f)]
    exact integral_nonneg fun k => b.re_inner_nonneg (eval P τ f k)
  · intro f h j
    change (∫ k : K, b.inner (eval P τ f k + eval P τ h k) (eval P τ j k) ∂μ) = _
    simp_rw [b.add_left]
    exact integral_add (hint f j) (hint h j)
  · intro f h c
    change (∫ k : K, b.inner (c • eval P τ f k) (eval P τ h k) ∂μ) = _
    simp_rw [b.smul_left]
    exact integral_const_mul _ _
  · intro f hf
    by_contra hne
    obtain ⟨x₀, hx₀⟩ := exists_eval_ne_zero P τ f hne
    let : InnerProductSpace.Core ℂ V := b
    let r : K → ℝ := fun k =>
      (b.inner (eval P τ f ((k : G) * x₀)) (eval P τ f ((k : G) * x₀))).re
    have hr0 : 0 ≤ r := fun k => b.re_inner_nonneg _
    have hrint : Integrable r μ := (hpair f f x₀).1.re
    have hrc : Continuous r :=
      ((pairing_isLocallyConstant P τ b f f).comp Complex.re).continuous.comp
        (continuous_subtype_val.mul continuous_const)
    have hr1 : 0 < r 1 := by
      simp only [r, Subgroup.coe_one, one_mul]
      exact lt_of_le_of_ne (b.re_inner_nonneg _)
        (fun hz => hx₀ ((InnerProductSpace.Core.normSq_eq_zero (𝕜 := ℂ)).mp hz.symm))
    have hrpos : 0 < ∫ k, r k ∂μ := by
      rw [integral_pos_iff_support_of_nonneg hr0 hrint]
      exact (hpos {k | 0 < r k} (isOpen_lt continuous_const hrc) hr1).trans_le
        (measure_mono fun k hk => by exact ne_of_gt hk)
    have hrzero : (∫ k, r k ∂μ) = 0 := by
      change (∫ k : K, RCLike.re
        (b.inner (eval P τ f ((k : G) * x₀)) (eval P τ f ((k : G) * x₀))) ∂μ) = 0
      rw [integral_re (hpair f f x₀).1, (hpair f f x₀).2, hf]
      rfl
    exact hrpos.ne' hrzero
  · intro g f h
    exact (hpair f h g).2

end Langlands.Induction

namespace Langlands.Aubert.General

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G))

/-- The coefficient pairing of two normalized induced functions transforms by
the full positive Haar modulus of conjugation on `U`. -/
theorem normalizedInduction_pairing_covariant
    (A : SmoothRep.{0, uG, uV} ℂ M) (b : InvariantPositiveForm A.representation)
    (f j : (normalizedInductionFunctor h hU).obj A) (q : P) (x : G) :
    b.inner (Induction.eval P (inducingRepresentation h hU A) f ((q : G) * x))
        (Induction.eval P (inducingRepresentation h hU A) j ((q : G) * x)) =
      (((HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0) : ℝ) : ℂ) *
        b.inner (Induction.eval P (inducingRepresentation h hU A) f x)
          (Induction.eval P (inducingRepresentation h hU A) j x) := by
  let : InnerProductSpace.Core ℂ A := b.toInnerProductCore
  rw [normalizedInductionFunctor_covariant, normalizedInductionFunctor_covariant,
    b.smul_left, InnerProductSpace.Core.inner_smul_right, b.invariant]
  have hreal :
      conj ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer q : ℂˣ) : ℂ) =
        ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer q : ℂˣ) : ℂ) := by
    simp only [HaarModulus.closedHalfCharacter, Jacquet.complexCharacter_apply,
      Complex.conj_ofReal]
  rw [hreal, ← mul_assoc, closedHalfCharacter_mul_self h hU q]

variable [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- A chosen positive form on actual normalized induction from a compact quotient.
The modular-character identity is the full parabolic identity. -/
def compactQuotientNormalizedInductionForm
    (hP : IsClosed (P : Set G)) [LocallyCompactSpace P]
    [CompactSpace (Induction.LeftQuotient P)]
    (hG : ∀ g : G, Measure.modularCharacter g = 1)
    (hδ : ∀ q : P, Measure.modularCharacter q =
      (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))
    (A : SmoothRep.{0, uG, uV} ℂ M) (b : InvariantPositiveForm A.representation) :
    InvariantPositiveForm ((normalizedInductionFunctor h hU).obj A).representation := by
  let hmeasure := Induction.exists_compactQuotient_measure hG P hP
  let μ := Classical.choose hmeasure
  have hpos := (Classical.choose_spec hmeasure).1
  have hscalar := (Classical.choose_spec hmeasure).2
  apply Induction.integralInvariantPositiveForm_of_pos P (inducingRepresentation h hU A)
    b.toInnerProductCore ⊤ μ hpos
  intro f j
  apply hscalar (fun x => b.inner (Induction.eval P (inducingRepresentation h hU A) f x)
    (Induction.eval P (inducingRepresentation h hU A) j x))
    (Induction.pairing_isLocallyConstant P _ b.toInnerProductCore f j)
  intro q x
  rw [normalizedInduction_pairing_covariant h hU A b f j q x, hδ q]

/-- Normalized induction from a compact quotient preserves unitarizability under
the ambient and parabolic modular-character identities. -/
theorem normalizedInductionFunctor_obj_isUnitarizable_of_compactSpace
    (hP : IsClosed (P : Set G)) [LocallyCompactSpace P]
    [CompactSpace (Induction.LeftQuotient P)]
    (hG : ∀ g : G, Measure.modularCharacter g = 1)
    (hδ : ∀ q : P, Measure.modularCharacter q =
      (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))
    (A : SmoothRep.{0, uG, uV} ℂ M) (hA : IsUnitarizable A.representation) :
    IsUnitarizable ((normalizedInductionFunctor h hU).obj A).representation := by
  obtain ⟨b⟩ := hA
  exact ⟨compactQuotientNormalizedInductionForm h hU hP hG hδ A b⟩

end Langlands.Aubert.General
