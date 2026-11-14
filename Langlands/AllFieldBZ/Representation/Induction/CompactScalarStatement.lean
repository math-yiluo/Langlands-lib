import Langlands.AllFieldBZ.Group.GL.BlockModulus
import Langlands.Representation.Induction.CompactScalarStatement

/-!
# All-field port of `Langlands.Representation.Induction.CompactScalarStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Induction.CompactScalarStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ
open Langlands.GeneralLinear
open MeasureTheory
open scoped NNReal
universe uF

/-- Existence of the right-invariant scalar compact-picture integral for every
standard block parabolic of a positive-rank general linear group. -/
def GLParabolicCompactScalarIntegralStatement : Prop :=
  ∀ (F : LocalFieldPackage.{uF}) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n),
      letI := T.generalLinearTopologicalGroup n
      ∃ K : OpenSubgroup (GeneralLinear n F.Carrier),
        IsCompact (K : Set (GeneralLinear n F.Carrier)) ∧
        (∀ g : GeneralLinear n F.Carrier,
          ∃ (q : B.parabolic F.Carrier) (k : K),
            g = (q : GeneralLinear n F.Carrier) * (k : GeneralLinear n F.Carrier)) ∧
        (letI : MeasurableSpace K := borel K
         ∃ μ : Measure K,
           μ.IsHaarMeasure ∧ IsProbabilityMeasure μ ∧
           ∀ φ : GeneralLinear n F.Carrier → ℂ, IsLocallyConstant φ →
             (∀ (q : B.parabolic F.Carrier) (x : GeneralLinear n F.Carrier),
               φ ((q : GeneralLinear n F.Carrier) * x) =
                 (((T.leviModulus B (B.leviProjection F.Carrier q) : ℝ≥0) : ℝ) : ℂ) *
                   φ x) →
             ∀ g : GeneralLinear n F.Carrier,
               Integrable (fun k : K => φ ((k : GeneralLinear n F.Carrier) * g)) μ ∧
               (∫ k : K, φ ((k : GeneralLinear n F.Carrier) * g) ∂μ) =
                 ∫ k : K, φ (k : GeneralLinear n F.Carrier) ∂μ)

end Langlands.AllFieldBZ
