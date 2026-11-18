import Langlands.Automorphic.GroupSchemeQuotientL2Integrated
import Langlands.Global.AdelicSplitCenterHaar
import Langlands.Global.AdelicSplitCenterMeasure
import Langlands.Analysis.OperatorIdeals
import Langlands.Analysis.OperatorTrace
import Langlands.Representation.Unitary.IntegratedOperator
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# Trace of `R(f)` on the positive quotient equals trace of `R(f¹)` on the norm-one quotient

Let `F` be a number field and `G` an affine group scheme over `F`, locally of finite type,
with comparison data `T, i, hi, I, e, hc`: a split torus `T` with a central homomorphism
`i : T → G` along which restriction of rational characters is injective with image of finite
index. Let `A⁺` be the positive real points of `T`, `G(𝔸_F)¹` the norm-one subgroup and
`G(F)` the rational points inside it. The Library's `L²` space is `L²(A⁺ G(F) \ G(𝔸_F))`,
with the integrated action `R(f)` of `f ∈ C_c(G(𝔸_F))`. Put `f¹(x) = ∫_{A⁺} f(a x) da` for
`x ∈ G(𝔸_F)¹`. Then `f¹` is continuous with compact support, and for every representation
`π` of `G(𝔸_F)¹` on `L²(G(F) \ G(𝔸_F)¹)` acting by right translation, `R(f)` is trace class
if and only if `π(f¹)` is, and then their traces agree.

Derived content: it makes precise the passage between functions on `G(𝔸_F)` and on
`A_G \ G(𝔸_F)` behind Getz–Hahn 2024, §18.4 (Corollary 18.4.1, printed p. 485). See
`PositiveQuotientTraceComparisonStatement.md`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Analysis.OperatorIdeals

namespace Langlands.TraceFormula

/-- For `f ∈ C_c(G(𝔸_F))`, the average `f¹(x) = ∫_{A⁺} f(a x) da` over the positive real
points of the central split torus (Library normalized Haar measure on `A⁺`) is continuous and
compactly supported on `G(𝔸_F)¹`. Moreover, for every isometric representation `π` of
`G(𝔸_F)¹` on `L²(G(F) \ G(𝔸_F)¹)` (Library quotient Haar measure) with strongly measurable
orbits that acts by right translation almost everywhere, the Library operator `R(f)` on
`L²(A⁺ G(F) \ G(𝔸_F))` is trace class if and only if `π(f¹)` is, and if `R(f)` is trace class
then `tr R(f) = tr π(f¹)`. Both operators are integrated vector by vector:
`π(f¹) v = ∫ f¹(x) • π(x) v dx`. -/
def PositiveQuotientTraceComparisonStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]
    (f : C_c(AdelicGroupPoints F G, ℂ)),
    let fOne : normOneSubgroup F G → ℂ := fun x =>
      ∫ a, f (positivePointMap F G T i a * x)
        ∂normalizedPositiveHaarMeasure F G T i hi I e hc
    Continuous fOne ∧ HasCompactSupport fOne ∧
    ∀ (h : Integrable f (Measure.haar : Measure (AdelicGroupPoints F G)))
      (hOne : Integrable fOne (Measure.haar : Measure (normOneSubgroup F G)))
      (π : normOneSubgroup F G →*
        (Lp ℂ 2 (normOneRationalQuotientHaarMeasure F G) →L[ℂ]
          Lp ℂ 2 (normOneRationalQuotientHaarMeasure F G)))
      (hπnorm : ∀ (g : normOneSubgroup F G) (φ : Lp ℂ 2 (normOneRationalQuotientHaarMeasure F G)),
        ‖π g φ‖ = ‖φ‖)
      (hπmeas : ∀ φ : Lp ℂ 2 (normOneRationalQuotientHaarMeasure F G),
        AEStronglyMeasurable (fun g => π g φ) (Measure.haar : Measure (normOneSubgroup F G))),
      (∀ (g : normOneSubgroup F G) (φ : Lp ℂ 2 (normOneRationalQuotientHaarMeasure F G)),
        (π g φ : NormOneRationalQuotient F G → ℂ) =ᵐ[normOneRationalQuotientHaarMeasure F G]
          fun q => φ (Langlands.QuotientIntegration.rightTranslate
            (rationalNormOneSubgroup F G) g q)) →
      (IsTraceClass (haarQuotientL2IntegratedAction F G T i hi I e hc Measure.haar f h) ↔
        IsTraceClass (Langlands.Analysis.integratedIsometricAction Measure.haar π hπnorm hπmeas
          fOne hOne)) ∧
      (IsTraceClass (haarQuotientL2IntegratedAction F G T i hi I e hc Measure.haar f h) →
        operatorTrace (haarQuotientL2IntegratedAction F G T i hi I e hc Measure.haar f h) =
          operatorTrace (Langlands.Analysis.integratedIsometricAction Measure.haar π hπnorm
            hπmeas fOne hOne))

end Langlands.TraceFormula
