import Langlands.Automorphic.GroupSchemeQuotientL2Integrated
import Langlands.Global.AdelicSplitCenterHaar
import Langlands.Global.AdelicSplitCenterMeasure
import Langlands.Analysis.OperatorIdeals
import Langlands.Analysis.OperatorTrace
import Langlands.Representation.Unitary.IntegratedOperator
import Langlands.TraceFormula.TwistedOrbital
import Langlands.TraceFormula.AdelicGroupAutomorphism
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# Twisted comparison of traces on the positive and the norm-one quotients

For a number field `F` and an affine group scheme `G` locally of finite type, take the
Library's central split torus comparison data. A finite-order automorphism `τ` fixing the
torus pointwise acts by `Θ` on `G(𝔸_F)` and `θ` on `G(𝔸_F)¹`. The proposition asserts
that `Θ` preserves `A⁺ G(F)` and that the inverse induced map preserves the positive
quotient measure, defining the pullback twist `I_Θ`. It compares `R(f) ∘ I_Θ` with
`π(f¹) ∘ I_θ`, where `f¹(x) = ∫_{A⁺} f(a x) da`, by trace-class equivalence and equality
of `operatorTrace` when either composite is trace class.

The comparison is derived from the adelic quotient description of Getz–Hahn 2024, §2.6,
and the twist in §18.5, equations (18.31)–(18.33), printed p. 487, and Corollary 18.5.1,
printed p. 488. The paired Markdown gives the relation to the case `A_G^θ = A_G`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.Automorphic.GroupSchemeFunctions
open Langlands.QuotientIntegration
open Langlands.Analysis.OperatorIdeals
open Langlands.TraceFormula.AdelicGroupAutomorphism

namespace Langlands.TraceFormula

/-- Let `τ` be a finite-order automorphism of the affine group scheme `G` over the number field
`F` that fixes the central split torus `i : T → G` (`i ≫ τ.hom = i`), and let `Θ = adelicAut F τ`
on `G(𝔸_F)` and `θ = normOneAut F τ` on `G(𝔸_F)¹`. Then `Θ` preserves the subgroup generated
by `G(F)` and the positive real points `A⁺` of `T`, and the inverse of the induced map on
`A⁺ G(F) \ G(𝔸_F)` preserves the Library quotient measure. Moreover, for every
`f ∈ C_c(G(𝔸_F))`, average to `f¹(x) = ∫_{A⁺} f(a x) da` on `G(𝔸_F)¹` using normalized
Haar measure on `A⁺` and take integrability witnesses for `f` and `f¹`. Let `π` act
isometrically on `L²(G(F) \ G(𝔸_F)¹)` with almost everywhere strongly measurable orbits
and the almost everywhere right translation formula. Then `R(f) ∘ I_Θ` is trace class
if and only if `π(f¹) ∘ I_θ` is, and their `operatorTrace` values agree when either is
trace class. The twists `I_Θ` and `I_θ` pull back along the inverse maps on their
respective quotients. -/
def PositiveQuotientTwistedTraceComparisonStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]
    (τ : Aut G) (hτ : IsOfFinOrder τ), i ≫ τ.hom = i →
    ∃ (hΘ : ∀ x, adelicAut F τ x ∈ positiveRationalSubgroup F G T i ↔
        x ∈ positiveRationalSubgroup F G T i)
      (hΘμ : MeasurePreserving
        (quotientAutomorphism (positiveRationalSubgroup F G T i) (adelicAut F τ) hΘ).symm
        (positiveRationalQuotientHaarMeasure F G T i)
        (positiveRationalQuotientHaarMeasure F G T i)),
    ∀ f : C_c(AdelicGroupPoints F G, ℂ),
    let fOne : normOneSubgroup F G → ℂ := fun x =>
      ∫ a, f (positivePointMap F G T i a * x)
        ∂normalizedPositiveHaarMeasure F G T i hi I e hc
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
          fun q => φ (rightTranslate (rationalNormOneSubgroup F G) g q)) →
      let RΘ := (haarQuotientL2IntegratedAction F G T i hi I e hc Measure.haar f h).comp
        (twistOperator (positiveRationalSubgroup F G T i) (adelicAut F τ) hΘ
          (positiveRationalQuotientHaarMeasure F G T i) hΘμ)
      let πθ := (Langlands.Analysis.integratedIsometricAction Measure.haar π hπnorm hπmeas
          fOne hOne).comp
        (twistOperator (rationalNormOneSubgroup F G) (normOneAut F τ)
          (normOneAut_mem_rationalNormOneSubgroup_iff F τ)
          (normOneRationalQuotientHaarMeasure F G)
          (measurePreserving_rationalQuotientAut_symm F τ hτ))
      (IsTraceClass RΘ ↔ IsTraceClass πθ) ∧
        (IsTraceClass RΘ → operatorTrace RΘ = operatorTrace πθ)

end Langlands.TraceFormula
