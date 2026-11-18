import Langlands.Automorphic.GroupSchemeFullAEL2Integrated
import Langlands.Automorphic.GroupSchemeParabolicMeasure
import Langlands.Analysis.OperatorIdeals
import Langlands.Analysis.OperatorTrace
import Langlands.TraceFormula.TwistedOrbital
import Langlands.Global.AdelicSplitCenterHaar
import Langlands.Global.AdelicGroupRationalTopology
import Langlands.Global.AdelicGroupPointTopology
import Langlands.Global.FiniteAdelicGL.LocalFactor
import Langlands.JacquetLanglands.RegularElliptic
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# The simple trace formula for `GL_n` over a number field

Let `F` be a number field, `G = GL_n` as a group scheme over `F`, and `[G]` the Library's
quotient of `G(𝔸_F)` by `G(F)` and the positive real points `A⁺` of a central split torus. Let
`f = f₁ * f₂` be a Haar convolution of compactly supported continuous functions on `G(𝔸_F)` whose
cuspidal operators `R_cusp(f₁)` and `R_cusp(f₂)` are Hilbert–Schmidt, where `f₂` integrates to
zero along every two-sided translate of the adelic unipotent radical of every proper rational
parabolic, and where the support of `f` is regular elliptic at one finite place `v`. Write
`f¹(x) = ∫_{A⁺} f(a x) da` on `G(𝔸_F)¹`. Then `R(f)` is trace class on `L²([G])`, and there are
finitely many pairwise non-conjugate rational elements `γ`, regular elliptic at `v`, such that

`tr R(f) = ∑_γ vol(G_γ(F) \ G_γ(𝔸_F)¹) · ∫_{G_γ(𝔸_F)¹ \ G(𝔸_F)¹} f¹(x⁻¹ γ x) dx`,

for all compatible choices of centralizer measures; the volumes are finite and the orbital
integrals converge absolutely.

Source: Getz–Hahn 2024, Corollary 18.4.1 (printed p. 485), a case of Theorem 18.2.5 (printed
p. 479). Getz–Hahn attribute the simple trace formula to Deligne and Kazhdan ([DKV84], [Rog83]
in their bibliography); those papers were not consulted. The hypotheses on `f` are the derived
form used in this project: see `GeneralLinearSimpleTraceFormulaStatement.md`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.Automorphic.GroupSchemeFunctions
open Langlands.QuotientIntegration Langlands.JacquetLanglands
open Langlands.Analysis.OperatorIdeals

namespace Langlands.TraceFormula

local instance generalLinearSimpleTraceIsAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance generalLinearSimpleTraceSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

set_option hygiene false in
/-- The `GL_n` group scheme over `F`, for the bound variables `F` and `n`. -/
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

/-- The simple trace formula for `GL_n` over a number field `F`, in the Library's group-scheme
form. Let `f = f₁ * f₂` be the Haar convolution of compactly supported continuous functions on
`GL_n(𝔸_F)` such that the Library's cuspidal operators `R_cusp(f₁)` and `R_cusp(f₂)` are
Hilbert–Schmidt, `f₂` integrates to zero along every two-sided translate of the adelic
unipotent radical of every proper rational parabolic, and every point of the support of `f` has
regular elliptic component at the finite place `v`. Let `f¹(x) = ∫ f(a x) da` be the average of
`f` over the positive real points `A⁺` of the central split torus, for the Library's normalized
Haar measure on `A⁺`, as a function on the norm-one subgroup `GL_n(𝔸_F)¹`. Then `f` is
integrable, `R(f)` is trace class on `L²([G])`, and there are finitely many rational norm-one
points `r j`, pairwise non-conjugate under the rational subgroup, regular elliptic at `v`, and
such that every rational norm-one point `q` with `f¹(x⁻¹ q x) ≠ 0` for some `x ∈ GL_n(𝔸_F)¹`
is conjugate under the rational subgroup to some `r j`. Moreover,
for all right-invariant Radon measures `μC j` on the centralizers `C j` of `r j` in
`GL_n(𝔸_F)¹` and all compatible quotient measures on `C j \ GL_n(𝔸_F)¹` and on
`(Γ ∩ C j) \ C j`, the volumes of `(Γ ∩ C j) \ C j` are finite, the orbit functions of `f¹` are
integrable, and `tr R(f) = ∑ j, vol((Γ ∩ C j) \ C j) · O_{r j}(f¹)`. -/
def GeneralLinearSimpleTraceFormulaStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (n : ℕ)
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive GLₙ)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ GLₙ)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F GLₙ)).IsMulRightInvariant],
    let μG : Measure (AdelicGroupPoints F GLₙ) := Measure.haar
    ∀ f₁ f₂ : C_c(AdelicGroupPoints F GLₙ, ℂ),
      (∀ h₁ : Integrable f₁ μG,
        IsHilbertSchmidt (fullAEL2CuspidalIntegratedAction F GLₙ hPD hG T i hi I e hc μG f₁ h₁)) →
      (∀ h₂ : Integrable f₂ μG,
        IsHilbertSchmidt (fullAEL2CuspidalIntegratedAction F GLₙ hPD hG T i hi I e hc μG f₂ h₂)) →
      (∀ (P : ProperRationalParabolic GLₙ) (x y : AdelicGroupPoints F GLₙ),
        ∫ m, f₂ (x * (m : AdelicGroupPoints F GLₙ) * y)
          ∂properParabolicHaarMeasure F GLₙ hPD hG P = 0) →
    let f : AdelicGroupPoints F GLₙ → ℂ := fun g => ∫ a, f₁ a * f₂ (a⁻¹ * g) ∂μG
    ∀ v : Langlands.Global.FinitePlace F,
      (∀ g ∈ tsupport f, IsRegularElliptic (FiniteAdelicGL.localProjection F n v
        (AdelicGL.finite F n (GeneralLinearGroupPoints.adelicHomeomorph F n g)))) →
    let fOne : normOneSubgroup F GLₙ → ℂ := fun x =>
      ∫ a, f (positivePointMap F GLₙ T i a * x)
        ∂normalizedPositiveHaarMeasure F GLₙ T i hi I e hc
    ∃ h : Integrable f μG,
      IsTraceClass (haarQuotientL2IntegratedAction F GLₙ T i hi I e hc μG f h) ∧
      ∃ (m : ℕ) (r : Fin m → rationalNormOneSubgroup F GLₙ),
        (∀ j k, IsTwistedConjugate (rationalNormOneSubgroup F GLₙ)
          (MonoidHom.id (normOneSubgroup F GLₙ)) (r j : normOneSubgroup F GLₙ)
          (r k : normOneSubgroup F GLₙ) → j = k) ∧
        (∀ j, IsRegularElliptic (FiniteAdelicGL.localProjection F n v
          (AdelicGL.finite F n (GeneralLinearGroupPoints.adelicHomeomorph F n
            ((r j : normOneSubgroup F GLₙ) : AdelicGroupPoints F GLₙ))))) ∧
        (∀ q ∈ rationalNormOneSubgroup F GLₙ,
          (∃ x : normOneSubgroup F GLₙ, fOne (x⁻¹ * q * x) ≠ 0) →
          ∃ j, IsTwistedConjugate (rationalNormOneSubgroup F GLₙ)
            (MonoidHom.id (normOneSubgroup F GLₙ)) (r j : normOneSubgroup F GLₙ) q) ∧
        ∀ [∀ j, MeasurableSpace (LeftQuotient (twistedCentralizer
              (MonoidHom.id (normOneSubgroup F GLₙ)) (r j : normOneSubgroup F GLₙ)))]
          [∀ j, BorelSpace (LeftQuotient (twistedCentralizer
              (MonoidHom.id (normOneSubgroup F GLₙ)) (r j : normOneSubgroup F GLₙ)))]
          [∀ j, MeasurableSpace (LeftQuotient ((rationalNormOneSubgroup F GLₙ).subgroupOf
              (twistedCentralizer (MonoidHom.id (normOneSubgroup F GLₙ))
                (r j : normOneSubgroup F GLₙ))))]
          [∀ j, BorelSpace (LeftQuotient ((rationalNormOneSubgroup F GLₙ).subgroupOf
              (twistedCentralizer (MonoidHom.id (normOneSubgroup F GLₙ))
                (r j : normOneSubgroup F GLₙ))))]
          (μC : ∀ j, Measure (twistedCentralizer (MonoidHom.id (normOneSubgroup F GLₙ))
              (r j : normOneSubgroup F GLₙ)))
          [∀ j, (μC j).IsMulRightInvariant] [∀ j, IsFiniteMeasureOnCompacts (μC j)]
          [∀ j, (μC j).IsOpenPosMeasure]
          (νC : ∀ j, Measure (LeftQuotient (twistedCentralizer
              (MonoidHom.id (normOneSubgroup F GLₙ)) (r j : normOneSubgroup F GLₙ))))
          (νΓC : ∀ j, Measure (LeftQuotient ((rationalNormOneSubgroup F GLₙ).subgroupOf
              (twistedCentralizer (MonoidHom.id (normOneSubgroup F GLₙ))
                (r j : normOneSubgroup F GLₙ))))),
          (∀ j, Langlands.QuotientIntegration.IsCompatible
            (twistedCentralizer (MonoidHom.id (normOneSubgroup F GLₙ))
              (r j : normOneSubgroup F GLₙ))
            (Measure.haar : Measure (normOneSubgroup F GLₙ)) (μC j) (νC j)) →
          (∀ j, Langlands.QuotientIntegration.IsCompatible
            ((rationalNormOneSubgroup F GLₙ).subgroupOf
              (twistedCentralizer (MonoidHom.id (normOneSubgroup F GLₙ))
                (r j : normOneSubgroup F GLₙ)))
            (μC j) Measure.count (νΓC j)) →
          (∀ j, νΓC j Set.univ ≠ ⊤) ∧
          (∀ j, Integrable (twistedOrbitFunction (MonoidHom.id (normOneSubgroup F GLₙ))
            (r j : normOneSubgroup F GLₙ) fOne) (νC j)) ∧
          operatorTrace (haarQuotientL2IntegratedAction F GLₙ T i hi I e hc μG f h) =
            ∑ j, ((νΓC j Set.univ).toReal : ℂ) *
              orbitalIntegral (r j : normOneSubgroup F GLₙ) (νC j) fOne

end Langlands.TraceFormula
