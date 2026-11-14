import Langlands.Representation.Induction.CompactScalarStatement
import Langlands.AllField.Group.GL.BlockModulusSupplement
/-!
# The scalar compact-picture integral for standard GL parabolics

This proposition specifies a compact open Iwasawa subgroup and one Haar
probability measure whose integral is invariant under every ambient right
translation of each locally constant full-modulus-covariant scalar function.
-/

namespace Langlands.AllField

open _root_.MeasureTheory
open Langlands.GeneralLinear
open scoped NNReal

universe uF

/-- Existence of the right-invariant scalar compact-picture integral for every
standard block parabolic of a positive-rank general linear group. -/
def GLParabolicCompactScalarIntegralStatement : Prop :=
  ∀ (F : Type uF) [Field F] (T : LocalFieldData F),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n),
      letI := T.generalLinearTopologicalGroup n
      ∃ K : OpenSubgroup (GeneralLinear n F),
        IsCompact (K : Set (GeneralLinear n F)) ∧
        (∀ g : GeneralLinear n F,
          ∃ (q : B.parabolic F) (k : K),
            g = (q : GeneralLinear n F) * (k : GeneralLinear n F)) ∧
        (letI : MeasurableSpace K := borel K
         ∃ μ : Measure K,
           μ.IsHaarMeasure ∧ IsProbabilityMeasure μ ∧
           ∀ φ : GeneralLinear n F → ℂ, IsLocallyConstant φ →
             (∀ (q : B.parabolic F) (x : GeneralLinear n F),
               φ ((q : GeneralLinear n F) * x) =
                 (((T.leviModulus B (B.leviProjection F q) : ℝ≥0) : ℝ) : ℂ) *
                   φ x) →
             ∀ g : GeneralLinear n F,
               Integrable (fun k : K => φ ((k : GeneralLinear n F) * g)) μ ∧
               (∫ k : K, φ ((k : GeneralLinear n F) * g) ∂μ) =
                 ∫ k : K, φ (k : GeneralLinear n F) ∂μ)

end Langlands.AllField
