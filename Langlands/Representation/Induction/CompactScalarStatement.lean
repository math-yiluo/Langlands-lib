import Langlands.Group.GL.BlockModulus
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# The scalar compact-picture integral for standard GL parabolics

This proposition specifies a compact open Iwasawa subgroup and one Haar
probability measure whose integral is invariant under every ambient right
translation of each locally constant full-modulus-covariant scalar function.
-/

namespace Langlands

open GeneralLinear MeasureTheory
open scoped NNReal

universe uF

/-- Existence of the right-invariant scalar compact-picture integral for every
standard block parabolic of a positive-rank general linear group. -/
def GLParabolicCompactScalarIntegralStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
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

end Langlands
