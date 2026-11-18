import Langlands.Group.GL.CartanQuotientCoverStatement
import Mathlib.MeasureTheory.Group.Measure

/-!
# Haar-volume bounds for Cartan cells modulo the center

The normalized Cartan cells partition the full central quotient. For every
Borel Haar measure, their masses and the masses of the cells for compact open
subgroups of the integral subgroup are comparable to the inverse upper-Borel
modulus, uniformly under common shifts of the exponents.
-/

open MeasureTheory

namespace Langlands.GeneralLinear.CartanQuotient

universe uF

/-- Two-sided Haar-volume bounds for actual Cartan cells on `GL_n(F)/Z`, with
compact openness of the standard integral subgroup, the normalized partition,
and the corresponding bounds and disjointness for compact open subgroups of
the integral subgroup. -/
def CartanQuotientVolumeStatement : Prop :=
  CartanQuotientCoverStatement.{uF} ∧
    ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
      (n : ℕ), 0 < n →
        letI := T.topology
        letI : MeasurableSpace (centralQuotient F n) := borel _
        IsCompact (maximalCompact T n : Set (GeneralLinear n F.Carrier)) ∧
        IsOpen (maximalCompact T n : Set (GeneralLinear n F.Carrier)) ∧
        ∀ (μ : Measure (centralQuotient F n)) [μ.IsHaarMeasure],
          (∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
            ∀ (lam : NormalizedTuple n) (c : ℤ),
              let exponents := shift lam.val c
              let s := cell T exponents
              MeasurableSet s ∧ 0 < μ s ∧ μ s < ⊤ ∧
                C₁ * (delta T exponents)⁻¹ ≤ (μ s).toReal ∧
                (μ s).toReal ≤ C₂ * (delta T exponents)⁻¹) ∧
          ∀ (H : Subgroup (GeneralLinear n F.Carrier)),
            H ≤ maximalCompact T n →
            IsCompact (H : Set (GeneralLinear n F.Carrier)) →
            IsOpen (H : Set (GeneralLinear n F.Carrier)) →
              (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
                ∀ (lam : NormalizedTuple n) (c : ℤ),
                  let exponents := shift lam.val c
                  let s := subgroupCell T H exponents
                  MeasurableSet s ∧ 0 < μ s ∧ μ s < ⊤ ∧
                    c₁ * (delta T exponents)⁻¹ ≤ (μ s).toReal ∧
                    (μ s).toReal ≤ c₂ * (delta T exponents)⁻¹) ∧
              Pairwise (fun (lam nu : NormalizedTuple n) =>
                Disjoint (subgroupCell T H lam.val) (subgroupCell T H nu.val))

end Langlands.GeneralLinear.CartanQuotient
