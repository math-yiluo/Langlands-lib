import Langlands.Automorphic.GroupSchemeFullAEL2Integrated
import Langlands.Automorphic.GroupSchemeParabolicMeasure
import Langlands.Analysis.OperatorIdeals
import Langlands.Analysis.OperatorTrace
import Langlands.TraceFormula.TwistedOrbital
import Langlands.TraceFormula.AdelicGroupAutomorphism
import Langlands.Global.AdelicGaloisTwistMap
import Langlands.Global.AdelicSplitCenterHaar
import Langlands.Global.AdelicGroupRationalTopology
import Langlands.Global.AdelicGroupPointTopology
import Langlands.GroupScheme.Reductive.GeneralLinear
import Langlands.BaseChange.Norm
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# The simple twisted trace formula for `Res_{L/K} GL_n` with rational σ-elliptic support

This is the formula of `GeneralLinearSimpleTwistedTraceFormulaStatement` with the same
operators, measures and geometric terms, under a different support hypothesis. The geometric
side runs over the rational twisted classes on whose adelic twisted orbit the averaged function
on the norm-one subgroup is nonzero somewhere. Each such class is required to be rationally
σ-elliptic: its rational norm is associated with a regular elliptic matrix over the base field
`K`. No ellipticity over `L` or over a completion of `L` is required. Support of the
convolution in the set where the norm is regular elliptic at a finite place of `L`, or where
the component at a finite place of `K` is σ-elliptic, implies this hypothesis.

Derived from Getz–Hahn (2024), §18.5 and Corollary 18.5.1 (printed pp. 486–488), with the
norm and σ-ellipticity conventions of Henniart–Lemaire (2011), I.2.2–I.2.3 (printed pp. 11–14),
and the indexing of the twisted geometric terms in their II.6.4 (printed pp. 120–121).
See the paired Markdown.
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
open Langlands.BaseChange

namespace Langlands.TraceFormula

local instance generalLinearRationalEllipticTwistedTraceIsAffine (K : Type u) [Field K] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

local instance generalLinearRationalEllipticTwistedTraceSmooth (K : Type u) [Field K] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

set_option hygiene false in
/-- The `GL_n` group scheme over `K`, for the bound variables `K` and `n`. -/
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

set_option hygiene false in
/-- The Weil restriction `Res_{L/K} GL_n`, for the bound variables `K`, `L` and `n`. -/
local notation "Wₙ" => weilGroup K L GLₙ

/-- The simple twisted trace formula for `W = Res_{L/K} GL_n` and a cyclic extension `L/K` of
number fields, with rational σ-elliptic support. The Galois twist fixes the image of the supplied
central split torus. The convolution factors have Hilbert–Schmidt cuspidal operators, and the
second factor has zero integral over every two-sided translate of each proper parabolic radical.
A rational point `q` of the norm-one subgroup contributes when the positive-torus average `fOne`
is nonzero somewhere on its norm-one twisted orbit. Every contributing `q` is required to
correspond under the adelic identification `Φ` to a matrix `δ ∈ GL_n(L)` that is σ-elliptic:
its norm is associated with a regular elliptic element of `GL_n(K)`.

The conclusion supplies the subgroup and quotient-measure preservation for the twist,
integrability of the convolution, and trace class of its operator. It chooses representatives of
distinct rational twisted classes, each contributing and rationally σ-elliptic, covering all
contributing classes. For every compatible choice of measures, the centralizer quotient volumes
are finite, the orbit functions are integrable, and the finite geometric sum equals the twisted
trace. -/
def GeneralLinearRationalEllipticTwistedTraceFormulaStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (L : Type u) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (l : ℕ), IsCyclicAlgebra σ l →
    ∀ (n : ℕ) (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive Wₙ)
    (T : CommGroupScheme (Spec (CommRingCat.of K))) (i : T.toGrp ⟶ Wₙ)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup K Wₙ)).IsMulRightInvariant],
    i ≫ (unitGaloisAut K L GLₙ σ).asIso.hom = i →
    let μG : Measure (AdelicGroupPoints K Wₙ) := Measure.haar
    let Θ : AdelicGroupPoints K Wₙ ≃ₜ* AdelicGroupPoints K Wₙ :=
      adelicAut K (unitGaloisAut K L GLₙ σ)
    let θ : normOneSubgroup K Wₙ ≃ₜ* normOneSubgroup K Wₙ :=
      normOneAut K (unitGaloisAut K L GLₙ σ)
    let Φ : AdelicGroupPoints K Wₙ → AdelicGL L n := fun g =>
      GeneralLinearGroupPoints.adelicHomeomorph L n
        (AdelicGroupPoints.map L (AffineWeil.unitBaseChange K L GLₙ)
          (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of L))
          (GroupScheme.GeneralLinear.baseChangeIso (Fin n) (Spec.algebraMap K L)).hom
          (AdelicGaloisUnit.weilAdelicEquiv K L GLₙ g))
    ∀ f₁ f₂ : C_c(AdelicGroupPoints K Wₙ, ℂ),
      (∀ h₁ : Integrable f₁ μG,
        IsHilbertSchmidt (fullAEL2CuspidalIntegratedAction K Wₙ hPD hG T i hi I e hc μG f₁ h₁)) →
      (∀ h₂ : Integrable f₂ μG,
        IsHilbertSchmidt (fullAEL2CuspidalIntegratedAction K Wₙ hPD hG T i hi I e hc μG f₂ h₂)) →
      (∀ (P : ProperRationalParabolic Wₙ) (x y : AdelicGroupPoints K Wₙ),
        ∫ m, f₂ (x * (m : AdelicGroupPoints K Wₙ) * y)
          ∂properParabolicHaarMeasure K Wₙ hPD hG P = 0) →
    let f : AdelicGroupPoints K Wₙ → ℂ := fun g => ∫ a, f₁ a * f₂ (a⁻¹ * g) ∂μG
    let fOne : normOneSubgroup K Wₙ → ℂ := fun x =>
      ∫ a, f (positivePointMap K Wₙ T i a * x)
        ∂normalizedPositiveHaarMeasure K Wₙ T i hi I e hc
    let contributes : normOneSubgroup K Wₙ → Prop := fun q =>
      ∃ x : normOneSubgroup K Wₙ, fOne (x⁻¹ * q * θ x) ≠ 0
    let rationalElliptic : normOneSubgroup K Wₙ → Prop := fun q =>
      ∃ δ : RationalGL L n, Φ (q : AdelicGroupPoints K Wₙ) = AdelicGL.rational L n δ ∧
        IsSigmaElliptic σ l δ
    (∀ q ∈ rationalNormOneSubgroup K Wₙ, contributes q → rationalElliptic q) →
    ∃ (hΘ : ∀ x, Θ x ∈ positiveRationalSubgroup K Wₙ T i ↔
        x ∈ positiveRationalSubgroup K Wₙ T i)
      (hΘμ : MeasurePreserving (quotientAutomorphism (positiveRationalSubgroup K Wₙ T i) Θ hΘ).symm
        (positiveRationalQuotientHaarMeasure K Wₙ T i)
        (positiveRationalQuotientHaarMeasure K Wₙ T i))
      (h : Integrable f μG),
      IsTraceClass (haarQuotientL2IntegratedAction K Wₙ T i hi I e hc μG f h) ∧
      ∃ (m : ℕ) (r : Fin m → rationalNormOneSubgroup K Wₙ),
        (∀ j k, IsTwistedConjugate (rationalNormOneSubgroup K Wₙ) θ
          (r j : normOneSubgroup K Wₙ) (r k : normOneSubgroup K Wₙ) → j = k) ∧
        (∀ j, contributes (r j : normOneSubgroup K Wₙ) ∧
          rationalElliptic (r j : normOneSubgroup K Wₙ)) ∧
        (∀ q ∈ rationalNormOneSubgroup K Wₙ, contributes q →
          ∃ j, IsTwistedConjugate (rationalNormOneSubgroup K Wₙ) θ
            (r j : normOneSubgroup K Wₙ) q) ∧
        ∀ [∀ j, MeasurableSpace (LeftQuotient (twistedCentralizer θ
              (r j : normOneSubgroup K Wₙ)))]
          [∀ j, BorelSpace (LeftQuotient (twistedCentralizer θ
              (r j : normOneSubgroup K Wₙ)))]
          [∀ j, MeasurableSpace (LeftQuotient ((rationalNormOneSubgroup K Wₙ).subgroupOf
              (twistedCentralizer θ (r j : normOneSubgroup K Wₙ))))]
          [∀ j, BorelSpace (LeftQuotient ((rationalNormOneSubgroup K Wₙ).subgroupOf
              (twistedCentralizer θ (r j : normOneSubgroup K Wₙ))))]
          (μC : ∀ j, Measure (twistedCentralizer θ (r j : normOneSubgroup K Wₙ)))
          [∀ j, (μC j).IsMulRightInvariant] [∀ j, IsFiniteMeasureOnCompacts (μC j)]
          [∀ j, (μC j).IsOpenPosMeasure]
          (νC : ∀ j, Measure (LeftQuotient (twistedCentralizer θ
              (r j : normOneSubgroup K Wₙ))))
          (νΓC : ∀ j, Measure (LeftQuotient ((rationalNormOneSubgroup K Wₙ).subgroupOf
              (twistedCentralizer θ (r j : normOneSubgroup K Wₙ))))),
          (∀ j, Langlands.QuotientIntegration.IsCompatible
            (twistedCentralizer θ (r j : normOneSubgroup K Wₙ))
            (Measure.haar : Measure (normOneSubgroup K Wₙ)) (μC j) (νC j)) →
          (∀ j, Langlands.QuotientIntegration.IsCompatible
            ((rationalNormOneSubgroup K Wₙ).subgroupOf
              (twistedCentralizer θ (r j : normOneSubgroup K Wₙ)))
            (μC j) Measure.count (νΓC j)) →
          (∀ j, νΓC j Set.univ ≠ ⊤) ∧
          (∀ j, Integrable (twistedOrbitFunction θ (r j : normOneSubgroup K Wₙ) fOne) (νC j)) ∧
          operatorTrace ((haarQuotientL2IntegratedAction K Wₙ T i hi I e hc μG f h).comp
            (twistOperator (positiveRationalSubgroup K Wₙ T i) Θ hΘ
              (positiveRationalQuotientHaarMeasure K Wₙ T i) hΘμ)) =
            ∑ j, ((νΓC j Set.univ).toReal : ℂ) *
              twistedOrbitalIntegral θ (r j : normOneSubgroup K Wₙ) (νC j) fOne

end Langlands.TraceFormula
