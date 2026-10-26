import Langlands.Representation.Induction.CompactIntegralForm
import Langlands.Representation.Induction.Parabolic
import Mathlib.MeasureTheory.Group.Measure

/-! Scalar compact integration gives the actual normalized induced form. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory
open scoped NNReal ComplexConjugate

namespace Langlands.PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (B.Levi F.Carrier) V)

private theorem normalized_pairing_covariant (b : InvariantPositiveForm σ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (f h : Induction.SmoothFunctions (B.parabolic F.Carrier)
      (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier))))
      (q : B.parabolic F.Carrier) (x : GeneralLinear n F.Carrier),
      b.inner (f.1.1 ((q : GeneralLinear n F.Carrier) * x))
        (h.1.1 ((q : GeneralLinear n F.Carrier) * x)) =
      (((T.leviModulus B (B.leviProjection F.Carrier q) : ℝ≥0) : ℝ) : ℂ) *
        b.inner (f.1.1 x) (h.1.1 x) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let : InnerProductSpace.Core ℂ V := b.toInnerProductCore
  intro f h q x
  change b.inner (Induction.eval _ _ f _) (Induction.eval _ _ h _) = _
  rw [T.normalizedParabolicInduced_covariant B σ f q x,
    T.normalizedParabolicInduced_covariant B σ h q x, b.smul_left,
    InnerProductSpace.Core.inner_smul_right, b.invariant]
  rw [Complex.conj_ofReal, ← mul_assoc]
  congr 1
  norm_cast
  exact NNReal.mul_self_sqrt _

/-- Conditional actual-Levi construction: the missing input is the scalar
compact integral theorem, with the positive full block modulus. -/
def normalizedIntegralForm (b : InvariantPositiveForm σ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (K : Subgroup (GeneralLinear n F.Carrier)) [MeasurableSpace K]
      (μ : Measure K) [μ.IsOpenPosMeasure],
      (∀ g : GeneralLinear n F.Carrier, ∃ (q : B.parabolic F.Carrier) (k : K),
        g = (q : GeneralLinear n F.Carrier) * (k : GeneralLinear n F.Carrier)) →
      (∀ φ : GeneralLinear n F.Carrier → ℂ, IsLocallyConstant φ →
        (∀ (q : B.parabolic F.Carrier) (x : GeneralLinear n F.Carrier),
          φ ((q : GeneralLinear n F.Carrier) * x) =
            (((T.leviModulus B (B.leviProjection F.Carrier q) : ℝ≥0) : ℝ) : ℂ) * φ x) →
        ∀ g : GeneralLinear n F.Carrier,
          Integrable (fun k : K => φ ((k : GeneralLinear n F.Carrier) * g)) μ ∧
          (∫ k : K, φ ((k : GeneralLinear n F.Carrier) * g) ∂μ) =
            ∫ k : K, φ k ∂μ) →
      InvariantPositiveForm (T.normalizedParabolicInduced B σ) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro K _ μ _ hPK hscalar
  refine Induction.integralInvariantPositiveForm _ _ b.toInnerProductCore K μ hPK ?_ ?_
  · intro f h
    simpa only [mul_one, Induction.eval] using
      (hscalar (fun x => b.inner (f.1.1 x) (h.1.1 x))
        (Induction.pairing_isLocallyConstant _ _ b.toInnerProductCore f h)
        (normalized_pairing_covariant T B σ b f h) 1).1
  · intro g f h
    exact (hscalar (fun x => b.inner (f.1.1 x) (h.1.1 x))
      (Induction.pairing_isLocallyConstant _ _ b.toInnerProductCore f h)
      (normalized_pairing_covariant T B σ b f h) g).2

end Langlands.PadicField.TopologicalData
