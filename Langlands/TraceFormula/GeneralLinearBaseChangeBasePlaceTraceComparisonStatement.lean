import Langlands.Automorphic.GroupSchemeFullAEL2Integrated
import Langlands.Automorphic.GroupSchemeParabolicMeasure
import Langlands.Analysis.OperatorIdeals
import Langlands.Analysis.OperatorTrace
import Langlands.TraceFormula.TwistedOrbital
import Langlands.TraceFormula.AdelicGroupAutomorphism
import Langlands.TraceFormula.GeneralLinearBaseChangeLocal
import Langlands.Global.AdelicGaloisTwistMap
import Langlands.Global.AdelicSplitCenterHaar
import Langlands.Global.AdelicGroupRationalTopology
import Langlands.Global.AdelicGroupPointTopology
import Langlands.Global.AdelicFunctoriality.Inclusion
import Langlands.Global.FiniteAdelicGL.LocalFactor
import Langlands.GroupScheme.Reductive.GeneralLinear
import Langlands.BaseChange.Norm
import Langlands.JacquetLanglands.RegularElliptic
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# Comparison of the simple trace formula for `GL_n` with its twisted form: the base-place form

This statement gives `tr (R(φ) ∘ I_θ) = c · tr R(f)` for the simple trace formula on `GL_n`
over a number field `K` and the simple twisted trace formula on `Res_{L/K} GL_n` over a cyclic
extension `L/K`, when both test functions are elliptic at one finite place `v` of `K`: the
component at `v` of every point of the closed support of the twisted test function is
σ_v-elliptic in `GL_n(K_v ⊗_K L)`, and the untwisted test function is supported in the regular
elliptic set at `v`. Its hypotheses compare global orbital integrals at norms of points regular
elliptic at `v` with a scalar `c` and require vanishing of the untwisted orbital integrals at the
points regular elliptic at `v` that are not norms.

It is the form of `GeneralLinearBaseChangeTraceComparisonStatement` in which the support
hypothesis on the twisted test function at a finite place of `L` is replaced by this condition
at the finite place `v` of `K`; all data and conclusions are those of that statement.

This is derived from the comparison of the simple trace formula with its twisted form in
Arthur–Clozel 1989, Chapter 1, formulas (4.4)–(4.6) (printed pp. 43–44) and §6.3 (printed
pp. 54–57), and Henniart–Lemaire 2011, II.6.4–II.6.6 (printed pp. 120–123), whose twisted
support condition is σ-ellipticity at a place of the base field. This module states the
proposition and does not prove it. See
`GeneralLinearBaseChangeBasePlaceTraceComparisonStatement.md`.
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
open Langlands.TraceFormula.AdelicGroupAutomorphism
open Langlands.BaseChange

namespace Langlands.TraceFormula

open scoped Langlands.TraceFormula.PlaceCompletion

local instance generalLinearBaseChangeBasePlaceComparisonIsAffine (K : Type u) [Field K]
    (n : ℕ) : IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

local instance generalLinearBaseChangeBasePlaceComparisonSmooth (K : Type u) [Field K]
    (n : ℕ) : Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

set_option hygiene false in
/-- The `GL_n` group scheme over `K`, for the bound variables `K` and `n`. -/
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

set_option hygiene false in
/-- The Weil restriction `Res_{L/K} GL_n`, for the bound variables `K`, `L` and `n`. -/
local notation "Wₙ" => weilGroup K L GLₙ

/-- Comparison of the simple twisted trace formula for `W = Res_{L/K} GL_n` with the simple
trace formula for `G = GL_n` over `K`, for a cyclic extension `L/K` of number fields with
`IsCyclicAlgebra σ l`, when both test functions are elliptic at the same finite place `v` of
`K`.

The data are those of `GeneralLinearBaseChangeTraceComparisonStatement`: the central split
tori `iW` (fixed by `unitGaloisAut K L GLₙ σ`) and `iG`, the identification `Φ` of `W(𝔸_K)`
with `GL_n(𝔸_L)`, the norm `N(g) = g Θ(g) ⋯ Θ^{l-1}(g)` for the full adelic automorphism `Θ`,
the entrywise adele inclusion `ι : GL_n(𝔸_K) → GL_n(𝔸_L)` and `ΦG`, the composite of `ι` with
the adelic point identification for `G`. The functions `φ = φ₁ * φ₂` on `W(𝔸_K)` and
`f = f₁ * f₂` on `G(𝔸_K)` satisfy the Hilbert–Schmidt conditions on their cuspidal operators
and the vanishing of the integrals of `φ₂` and `f₂` along the two-sided translates of the
unipotent radicals of the proper rational parabolics. Unlike in that statement, there is no
place of `L`: for one finite place `v` of `K`, for every `g ∈ tsupport φ` the component of `g`
at `v`, as a matrix in `GL_n(K_v ⊗_K L)` via `localPointsEquiv`, is σ_v-elliptic for
`σ_v = localGalois K L σ (.inr v)`, and for every `g ∈ tsupport f` the component of `g` at `v`
is regular elliptic in `GL_n(K_v)`. Let `φ¹` and `f¹` be the averages of `φ` and `f` over the
positive real points of the two tori.

Suppose that the following conditions hold for a constant `c`.

* for all rational norm-one points `r` of `W` and `q` of `G` and every `y ∈ GL_n(L)` with
  `Φ(N(r)) y = y ΦG(q)`, where `q` is regular elliptic at `v`, every isomorphism `e` from the
  `θ`-centralizer of `r` in `W(𝔸_K)¹` onto the centralizer of `q` in `G(𝔸_K)¹` with
  `ΦG(e(x)) = y⁻¹ Φ(x) y`, every right-invariant measure `μr` on the first that is finite on
  compacts and positive on nonempty open sets, every right-invariant `μq = e_* μr` on the
  second, and all compatible quotient measures `νr` and `νq`, the twisted orbital integral of
  `φ¹` at `r` for `νr` equals `c` times the orbital integral of `f¹` at `q` for `νq`. Here `θ`
  is the restriction of `Θ` to `W(𝔸_K)¹`.
* for every rational norm-one point `q` of `G` regular elliptic at `v` such that no `Φ(N(r))`
  with `r` a rational norm-one point of `W` is conjugate to `ΦG(q)` by an element of
  `GL_n(L)`, the orbital integral of `f¹` at `q` vanishes for every right-invariant
  centralizer measure finite on compacts and positive on nonempty open sets and every
  compatible quotient measure.

Then `Θ` preserves the subgroup generated by `W(K)` and the positive real points. The
inverse of the induced automorphism of `[W]` preserves its quotient measure. The functions
`φ` and `f` are integrable, the operators `R(φ)` and `R(f)` are trace class, and
`tr (R(φ) ∘ I_θ) = c · tr R(f)`. -/
def GeneralLinearBaseChangeBasePlaceTraceComparisonStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (L : Type u) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (l : ℕ), IsCyclicAlgebra σ l →
    ∀ (n : ℕ) (hPD : ParabolicDynamicStatement.{u})
    (hW : IsConnectedReductive Wₙ)
    (TW : CommGroupScheme (Spec (CommRingCat.of K))) (iW : TW.toGrp ⟶ Wₙ)
    (hiW : Function.Injective (characterRestrict iW))
    [(characterRestrict iW).range.FiniteIndex]
    (IW : Type u) [Fintype IW]
    (eW : TW.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) IW) (hcW : IsCentral iW)
    [(Measure.haar : Measure (normOneSubgroup K Wₙ)).IsMulRightInvariant],
    iW ≫ (unitGaloisAut K L GLₙ σ).asIso.hom = iW →
    ∀ (hG : IsConnectedReductive GLₙ)
    (TG : CommGroupScheme (Spec (CommRingCat.of K))) (iG : TG.toGrp ⟶ GLₙ)
    (hiG : Function.Injective (characterRestrict iG))
    [(characterRestrict iG).range.FiniteIndex]
    (IG : Type u) [Fintype IG]
    (eG : TG.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) IG) (hcG : IsCentral iG)
    [(Measure.haar : Measure (normOneSubgroup K GLₙ)).IsMulRightInvariant],
    let μW : Measure (AdelicGroupPoints K Wₙ) := Measure.haar
    let μG : Measure (AdelicGroupPoints K GLₙ) := Measure.haar
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
    let N : AdelicGroupPoints K Wₙ → AdelicGroupPoints K Wₙ := fun g =>
      ((List.range l).map fun k => adelicAut K (unitGaloisAut K L GLₙ σ ^ k) g).prod
    let incl : AdelicGL K n →* AdelicGL L n :=
      Matrix.GeneralLinearGroup.map (AdelicFunctoriality.adeleInclusion (K := K) (L := L))
    let ΦG : AdelicGroupPoints K GLₙ → AdelicGL L n := fun g =>
      incl (GeneralLinearGroupPoints.adelicHomeomorph K n g)
    ∀ φ₁ φ₂ : C_c(AdelicGroupPoints K Wₙ, ℂ),
      (∀ h₁ : Integrable φ₁ μW,
        IsHilbertSchmidt
          (fullAEL2CuspidalIntegratedAction K Wₙ hPD hW TW iW hiW IW eW hcW μW φ₁ h₁)) →
      (∀ h₂ : Integrable φ₂ μW,
        IsHilbertSchmidt
          (fullAEL2CuspidalIntegratedAction K Wₙ hPD hW TW iW hiW IW eW hcW μW φ₂ h₂)) →
      (∀ (P : ProperRationalParabolic Wₙ) (x y : AdelicGroupPoints K Wₙ),
        ∫ m, φ₂ (x * (m : AdelicGroupPoints K Wₙ) * y)
          ∂properParabolicHaarMeasure K Wₙ hPD hW P = 0) →
    let φ : AdelicGroupPoints K Wₙ → ℂ := fun g => ∫ a, φ₁ a * φ₂ (a⁻¹ * g) ∂μW
    ∀ v : Langlands.Global.FinitePlace K,
      (∀ g ∈ tsupport φ, IsSigmaElliptic (localGalois K L σ (.inr v)) l
        (localPointsEquiv K L n (.inr v) (AdelicGroupPoints.atPlace K Wₙ (.inr v) g))) →
    ∀ f₁ f₂ : C_c(AdelicGroupPoints K GLₙ, ℂ),
      (∀ h₁ : Integrable f₁ μG,
        IsHilbertSchmidt
          (fullAEL2CuspidalIntegratedAction K GLₙ hPD hG TG iG hiG IG eG hcG μG f₁ h₁)) →
      (∀ h₂ : Integrable f₂ μG,
        IsHilbertSchmidt
          (fullAEL2CuspidalIntegratedAction K GLₙ hPD hG TG iG hiG IG eG hcG μG f₂ h₂)) →
      (∀ (P : ProperRationalParabolic GLₙ) (x y : AdelicGroupPoints K GLₙ),
        ∫ m, f₂ (x * (m : AdelicGroupPoints K GLₙ) * y)
          ∂properParabolicHaarMeasure K GLₙ hPD hG P = 0) →
    let f : AdelicGroupPoints K GLₙ → ℂ := fun g => ∫ a, f₁ a * f₂ (a⁻¹ * g) ∂μG
    (∀ g ∈ tsupport f, IsRegularElliptic (FiniteAdelicGL.localProjection K n v
      (AdelicGL.finite K n (GeneralLinearGroupPoints.adelicHomeomorph K n g)))) →
    let φOne : normOneSubgroup K Wₙ → ℂ := fun x =>
      ∫ a, φ (positivePointMap K Wₙ TW iW a * x)
        ∂normalizedPositiveHaarMeasure K Wₙ TW iW hiW IW eW hcW
    let fOne : normOneSubgroup K GLₙ → ℂ := fun x =>
      ∫ a, f (positivePointMap K GLₙ TG iG a * x)
        ∂normalizedPositiveHaarMeasure K GLₙ TG iG hiG IG eG hcG
    ∀ c : ℂ,
      (∀ r ∈ rationalNormOneSubgroup K Wₙ, ∀ q ∈ rationalNormOneSubgroup K GLₙ,
        ∀ y : GL (Fin n) L,
        Φ (N (r : AdelicGroupPoints K Wₙ)) * AdelicGL.rational L n y =
            AdelicGL.rational L n y * ΦG (q : AdelicGroupPoints K GLₙ) →
        IsRegularElliptic (FiniteAdelicGL.localProjection K n v
          (AdelicGL.finite K n (GeneralLinearGroupPoints.adelicHomeomorph K n
            (q : AdelicGroupPoints K GLₙ)))) →
        ∀ (e : twistedCentralizer θ r ≃*
            twistedCentralizer (MonoidHom.id (normOneSubgroup K GLₙ)) q),
          (∀ x : twistedCentralizer θ r,
            ΦG (((e x : normOneSubgroup K GLₙ)) : AdelicGroupPoints K GLₙ) =
              (AdelicGL.rational L n y)⁻¹ *
                Φ ((x : normOneSubgroup K Wₙ) : AdelicGroupPoints K Wₙ) *
                  AdelicGL.rational L n y) →
        ∀ [MeasurableSpace (LeftQuotient (twistedCentralizer θ r))]
          [BorelSpace (LeftQuotient (twistedCentralizer θ r))]
          (μr : Measure (twistedCentralizer θ r))
          [μr.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μr] [μr.IsOpenPosMeasure]
          (νr : Measure (LeftQuotient (twistedCentralizer θ r))),
          Langlands.QuotientIntegration.IsCompatible (twistedCentralizer θ r)
            (Measure.haar : Measure (normOneSubgroup K Wₙ)) μr νr →
        ∀ [MeasurableSpace (LeftQuotient
              (twistedCentralizer (MonoidHom.id (normOneSubgroup K GLₙ)) q))]
          [BorelSpace (LeftQuotient
              (twistedCentralizer (MonoidHom.id (normOneSubgroup K GLₙ)) q))]
          (μq : Measure (twistedCentralizer (MonoidHom.id (normOneSubgroup K GLₙ)) q))
          [μq.IsMulRightInvariant]
          (νq : Measure (LeftQuotient
              (twistedCentralizer (MonoidHom.id (normOneSubgroup K GLₙ)) q))),
          μr.map e = μq →
          Langlands.QuotientIntegration.IsCompatible
            (twistedCentralizer (MonoidHom.id (normOneSubgroup K GLₙ)) q)
            (Measure.haar : Measure (normOneSubgroup K GLₙ)) μq νq →
          twistedOrbitalIntegral θ r νr φOne = c * orbitalIntegral q νq fOne) →
      (∀ q ∈ rationalNormOneSubgroup K GLₙ,
        IsRegularElliptic (FiniteAdelicGL.localProjection K n v
          (AdelicGL.finite K n (GeneralLinearGroupPoints.adelicHomeomorph K n
            (q : AdelicGroupPoints K GLₙ)))) →
        (∀ r ∈ rationalNormOneSubgroup K Wₙ, ∀ y : GL (Fin n) L,
          Φ (N (r : AdelicGroupPoints K Wₙ)) * AdelicGL.rational L n y ≠
            AdelicGL.rational L n y * ΦG (q : AdelicGroupPoints K GLₙ)) →
        ∀ [MeasurableSpace (LeftQuotient
              (twistedCentralizer (MonoidHom.id (normOneSubgroup K GLₙ)) q))]
          [BorelSpace (LeftQuotient
              (twistedCentralizer (MonoidHom.id (normOneSubgroup K GLₙ)) q))]
          (μq : Measure (twistedCentralizer (MonoidHom.id (normOneSubgroup K GLₙ)) q))
          [μq.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μq] [μq.IsOpenPosMeasure]
          (νq : Measure (LeftQuotient
              (twistedCentralizer (MonoidHom.id (normOneSubgroup K GLₙ)) q))),
          Langlands.QuotientIntegration.IsCompatible
            (twistedCentralizer (MonoidHom.id (normOneSubgroup K GLₙ)) q)
            (Measure.haar : Measure (normOneSubgroup K GLₙ)) μq νq →
          orbitalIntegral q νq fOne = 0) →
      ∃ (hΘ : ∀ x, Θ x ∈ positiveRationalSubgroup K Wₙ TW iW ↔
          x ∈ positiveRationalSubgroup K Wₙ TW iW)
        (hΘμ : MeasurePreserving
          (quotientAutomorphism (positiveRationalSubgroup K Wₙ TW iW) Θ hΘ).symm
          (positiveRationalQuotientHaarMeasure K Wₙ TW iW)
          (positiveRationalQuotientHaarMeasure K Wₙ TW iW))
        (hφ : Integrable φ μW) (hf : Integrable f μG),
        IsTraceClass (haarQuotientL2IntegratedAction K Wₙ TW iW hiW IW eW hcW μW φ hφ) ∧
        IsTraceClass (haarQuotientL2IntegratedAction K GLₙ TG iG hiG IG eG hcG μG f hf) ∧
        operatorTrace ((haarQuotientL2IntegratedAction K Wₙ TW iW hiW IW eW hcW μW φ hφ).comp
            (twistOperator (positiveRationalSubgroup K Wₙ TW iW) Θ hΘ
              (positiveRationalQuotientHaarMeasure K Wₙ TW iW) hΘμ)) =
          c * operatorTrace (haarQuotientL2IntegratedAction K GLₙ TG iG hiG IG eG hcG μG f hf)

end Langlands.TraceFormula
