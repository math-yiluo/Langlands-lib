import Langlands.Analysis.Local.QuotientMeasure
import Langlands.Analysis.OperatorIdeals
import Langlands.Geometry.Manifold.LinearLieGroup.Realization
import Langlands.Representation.Archimedean.GardingFunctionals
import Langlands.Representation.Unitary.IntegratedOperator
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# Trace class of smooth compactly supported weights on a compact quotient

Two proposition definitions, beside `CompactQuotientConvolutionTraceClassStatement`:

* `CompactQuotientSmoothTraceClassStatement`: for a Lie group `G` with a closed linear realization
  and a compact quotient `H \ G`, every smooth compactly supported weight is integrable and
  integrates the right regular action on `L²(H \ G)` to a trace-class operator;
* `CompactQuotientProductSmoothTraceClassStatement`: the same on `A × B`, with `A` such a Lie group
  and `B` locally compact, Hausdorff and second countable, for weights with smooth slices that are
  right invariant under a compact open subgroup of `B`.

They are proved from `CompactQuotientConvolutionTraceClassStatement` in
`CompactQuotientSmoothTraceClassReduction`.
-/

noncomputable section

universe uE uG uA uB

namespace Langlands.QuotientIntegration

open MeasureTheory
open scoped CompactlySupported Manifold ContDiff

/-- On a compact left coset space of a Lie group `G` with a closed linear realization, every smooth
compactly supported weight `f` is integrable and integrates the right translation action to a
trace-class operator. The setting is that of `CompactQuotientConvolutionTraceClassStatement`, with
a left Haar measure `μG`. -/
def CompactQuotientSmoothTraceClassStatement : Prop :=
  ∀ {E : Type uE} {G : Type uG} [NormedAddCommGroup E] [NormedSpace ℝ E] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace E G] [LieGroup 𝓘(ℝ, E) ∞ G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {𝔸 : Type uA} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
    {ρ : G →* 𝔸ˣ}, LinearLieGroup.IsClosedLinearRealization 𝓘(ℝ, E) ρ →
    ∀ (H : Subgroup G) (_hH : IsClosed (H : Set G))
    [MeasurableSpace H] [BorelSpace H]
    (μH : Measure H) [SFinite μH] [μH.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μH]
    [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
    (μG : Measure G) [μG.IsHaarMeasure]
    (ν : Measure (LeftQuotient H)) [IsFiniteMeasureOnCompacts ν]
    (_hν : IsCompatible H μG μH ν), CompactSpace (LeftQuotient H) →
    ∀ (π : G →* (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν))
      (hπnorm : ∀ (g : G) (φ : Lp ℂ 2 ν), ‖π g φ‖ = ‖φ‖)
      (hπmeas : ∀ φ : Lp ℂ 2 ν, AEStronglyMeasurable (fun g => π g φ) μG),
      (∀ (g : G) (φ : Lp ℂ 2 ν),
        (π g φ : LeftQuotient H → ℂ) =ᵐ[ν] fun q => φ (rightTranslate H g q)) →
      ∀ f : Langlands.Archimedean.smoothCompactKernels E G,
        ∃ h : Integrable f.val μG,
          Langlands.Analysis.OperatorIdeals.IsTraceClass
            (Langlands.Analysis.integratedIsometricAction μG π hπnorm hπmeas f.val h)

/-- The same for a product `A × B` of a Lie group `A` with a closed linear realization and a
locally compact Hausdorff second countable group `B`, for compactly supported continuous weights
with smooth slices `a ↦ f (a, b)` that are right invariant under a compact open subgroup of `B`
(the weights of `Langlands.Analysis.DixmierMalliavin.exists_eq_sum_convolutionIntegral_prod`). -/
def CompactQuotientProductSmoothTraceClassStatement : Prop :=
  ∀ {E : Type uE} {A : Type uG} {B : Type uB} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [ChartedSpace E A]
    [LieGroup 𝓘(ℝ, E) ∞ A] [T2Space A] [LocallyCompactSpace A] [MeasurableSpace A] [BorelSpace A]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [LocallyCompactSpace B] [T2Space B]
    [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]
    {𝔸 : Type uA} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
    {ρ : A →* 𝔸ˣ}, LinearLieGroup.IsClosedLinearRealization 𝓘(ℝ, E) ρ →
    ∀ (H : Subgroup (A × B)) (_hH : IsClosed (H : Set (A × B)))
    [MeasurableSpace H] [BorelSpace H]
    (μH : Measure H) [SFinite μH] [μH.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μH]
    [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
    (μG : Measure (A × B)) [μG.IsHaarMeasure]
    (ν : Measure (LeftQuotient H)) [IsFiniteMeasureOnCompacts ν]
    (_hν : IsCompatible H μG μH ν), CompactSpace (LeftQuotient H) →
    ∀ (π : A × B →* (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν))
      (hπnorm : ∀ (g : A × B) (φ : Lp ℂ 2 ν), ‖π g φ‖ = ‖φ‖)
      (hπmeas : ∀ φ : Lp ℂ 2 ν, AEStronglyMeasurable (fun g => π g φ) μG),
      (∀ (g : A × B) (φ : Lp ℂ 2 ν),
        (π g φ : LeftQuotient H → ℂ) =ᵐ[ν] fun q => φ (rightTranslate H g q)) →
      ∀ (f : C_c(A × B, ℂ)), (∀ b, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ fun a => f (a, b)) →
      ∀ (V : Subgroup B), IsOpen (V : Set B) → IsCompact (V : Set B) →
      (∀ x, ∀ v ∈ V, f (x * (1, v)) = f x) →
        ∃ h : Integrable f μG,
          Langlands.Analysis.OperatorIdeals.IsTraceClass
            (Langlands.Analysis.integratedIsometricAction μG π hπnorm hπmeas f h)

end Langlands.QuotientIntegration
