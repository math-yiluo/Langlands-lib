import Langlands.Global.AdelicParabolicSpectrum
import Langlands.Global.AdelicRestrictionSplitCentreCanonical
import Langlands.Global.AdelicSplitCenterHaarIndependence
import Langlands.Global.AdelicLogSection
import Langlands.Global.AdelicLocalFinitenessStatement
import Langlands.Global.AdelicGroupRationalTopology
import Langlands.Global.AdelicGroupPointTopology
import Langlands.Global.FiniteAdelicGL.LocalFactor
import Langlands.Automorphic.GroupSchemeRestrictionQuotientL2Continuity
import Langlands.GroupScheme.FiniteAlgebraUnits
import Langlands.JacquetLanglands.RegularElliptic
import Langlands.TraceFormula.TwistedOrbital
import Langlands.Analysis.OperatorIdeals
import Langlands.Analysis.OperatorTrace

/-!
# The simple trace formula comparison between `GL_n` and the units of a division algebra

Let `F` be a number field, `A` a central division algebra of dimension `n²` over `F`,
`G' = Aˣ` its unit group scheme and `G = GL_n`. For smooth compactly supported test functions
`f'` on `G'(𝔸_F)` and `f` on `G(𝔸_F)` such that `f` has regular elliptic support at two distinct
finite places, the averaged function `f'¹` vanishes on the conjugates of the rational elements
whose reduced characteristic polynomial is not separable, the global orbital integrals match at
rational elements with the same (reduced) characteristic polynomial, and those of `f` vanish at
the regular elliptic classes that do not come from `A`, the statement
`DivisionAlgebraSimpleTraceComparisonStatement` asserts that `R'(f')` on `L²([G'])` and
`R_disc(f)` on `L²_disc([G])` are trace class with equal traces.

This module also defines the operators `canonicalIntegratedAction` (`R(f)` on the canonical
`L²([G])`), `canonicalDiscreteIntegratedAction` (its compression `R_disc(f)` to
`discreteSpectrum`), the average `canonicalNormOneAverage` (`f¹` on `G(𝔸_F)¹`) and the unit
`finiteAlgebraRationalUnit` of `A` attached to a rational point of `G'`.

The statement is derived from Deligne–Kazhdan–Vignéras 1984, §B.1.a and §C.1 (printed pp. 78
and 90–91), Arthur 1988, Corollary 7.5 (printed p. 541), Arthur–Clozel 1989, Chapter 2,
Theorems A and B (printed pp. 108 and 134), and Getz–Hahn 2024, §18.4 and Theorems 9.1.2 and
9.1.4 (printed pp. 485 and 241–242); it is not proved here. See
`DivisionAlgebraSimpleTraceComparisonStatement.md`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.RestrictionSplitCentre Langlands.Global.PositiveRealTorus
open Langlands.GroupScheme Langlands.JacquetLanglands Langlands.CentralSimple
open Langlands.QuotientIntegration
open Langlands.Analysis.OperatorIdeals

namespace Langlands.TraceFormula

section Canonical

variable (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- The integrated right regular action `R(f) φ = ∫ f(g) R(g) φ dg` on the canonical
`L²([G])`, `[G] = A_G G(F) \ G(𝔸_F)`, for `Measure.haar` on `G(𝔸_F)`. It is the Library's
`splitComponentL2IntegratedAction` (hence `rationalQuotientL2IntegratedAction` and
`integratedIsometricAction`) for the canonical split components of `Res_{F/ℚ} G` and `G`;
the right action it integrates is `canonicalL2RightAction F G centralSplitTorusCharacter hG`. -/
def canonicalIntegratedAction (hG : IsConnectedReductive G) (f : AdelicGroupPoints F G → ℂ)
    (hf : Integrable f (Measure.haar : Measure (AdelicGroupPoints F G))) :
    Lp ℂ 2 (canonicalMeasure F G) →L[ℂ] Lp ℂ 2 (canonicalMeasure F G) :=
  haveI := canonical_finiteIndex F G hG
  haveI := AdelicGroupPoints.normOneHaarRightInvariant F G hG.smooth hG.connectedSpace
  splitComponentL2IntegratedAction F G
    (canonical_characterRestrict_injective F G centralSplitTorusCharacter hG)
    (isSplitComponent_canonicalRestrictionComponent F G)
    (isSplitComponent_canonicalComponent F G) Measure.haar f hf

/-- The discrete spectrum `L²_disc([G])` is a closed subspace of `L²([G])`, hence complete. -/
instance discreteSpectrum_completeSpace (hG : IsConnectedReductive G) :
    CompleteSpace (discreteSpectrum F G hG) :=
  Submodule.topologicalClosure.completeSpace _

/-- The compression `R_disc(f) = P_disc ∘ R(f) ∘ ι_disc` of `canonicalIntegratedAction` to
the discrete spectrum `L²_disc([G]) = discreteSpectrum F G hG`, as an operator on that
subspace; `P_disc` is the orthogonal projection onto it and `ι_disc` its inclusion. -/
def canonicalDiscreteIntegratedAction (hG : IsConnectedReductive G)
    (f : AdelicGroupPoints F G → ℂ)
    (hf : Integrable f (Measure.haar : Measure (AdelicGroupPoints F G))) :
    discreteSpectrum F G hG →L[ℂ] discreteSpectrum F G hG :=
  (discreteSpectrum F G hG).orthogonalProjectionOnto ∘L
    canonicalIntegratedAction F G hG f hf ∘L (discreteSpectrum F G hG).subtypeL

/-- The average `f¹(x) = ∫_{A_G} f(a x) da` of `f` over the positive real points `A_G` of the
canonical split component of `G`, as a function on the norm-one subgroup `G(𝔸_F)¹`. Here `da`
is `intrinsicPositiveHaarMeasure`, the Haar measure on `A_G` whose product with
`Measure.haar` on `G(𝔸_F)¹` is `Measure.haar` on `G(𝔸_F)` under multiplication. -/
def canonicalNormOneAverage (hG : IsConnectedReductive G) (f : AdelicGroupPoints F G → ℂ) :
    normOneSubgroup F G → ℂ :=
  haveI := canonical_finiteIndex F G hG
  fun x => ∫ a, f (positivePointMap F G (canonicalTorus F G) (canonicalComponent F G) a *
      (x : AdelicGroupPoints F G))
    ∂intrinsicPositiveHaarMeasure F G (canonicalTorus F G) (canonicalComponent F G)
      (canonical_characterRestrict_injective F G centralSplitTorusCharacter hG)
      (isSplitComponent_canonicalComponent F G).1.2
      (isSplitComponent_canonicalComponent F G).1.1.1

end Canonical

/-- The unit of `A` given by a rational point of the unit group scheme
`FiniteAlgebraUnits.groupScheme (Module.finBasis F A)`: the point in `(F ⊗[F] A)ˣ` given by
`FiniteAlgebraUnits.affinePointsEquiv` over `F`, followed by `F ⊗[F] A ≃ A`. Composed with
`GaloisPointComparison.rationalCoeffEquiv` it is `FiniteAlgebraUnits.rationalPointsEquiv`. -/
def finiteAlgebraRationalUnit {F A : Type} [Field F] [NumberField F] [Ring A] [Algebra F A]
    [FiniteDimensional F A]
    (r : RationalGroupPoints F (FiniteAlgebraUnits.groupScheme (Module.finBasis F A))) : Aˣ :=
  Units.map (Algebra.TensorProduct.lid F A).toMonoidHom
    (FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis F A) (CommAlgCat.of F F) r)

local instance divisionAlgebraComparisonIsAffine (F : Type) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance divisionAlgebraComparisonSmooth (F : Type) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

set_option hygiene false in
/-- The `GL_n` group scheme over `F`, for the bound variables `F` and `n`. -/
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

set_option hygiene false in
/-- The unit group scheme `G'` of `A`, for the bound variables `F` and `A`. -/
local notation "Gₐ" => FiniteAlgebraUnits.groupScheme (Module.finBasis F A)

/-- The simple trace formula comparison between `G = GL_n` and the unit group `G' = Aˣ` of a
central division algebra `A` of dimension `n²` over a number field `F`.

Let `p₁ ≠ p₂` be finite places of `F`, and let `f'` on `G'(𝔸_F)` and `f` on `G(𝔸_F)` be
smooth compactly supported test functions (`IsAdelicTestFunction`). Write `f'¹`, `f¹` for their
averages over the canonical split centres (`canonicalNormOneAverage`), `P(r)` for the
characteristic polynomial of a rational point `r` of `G` and `P'(r')` for the reduced
characteristic polynomial (`reducedCharpoly`) of the unit of `A` given by a rational point
`r'` of `G'`. Assume:

1. every point of `tsupport f` has regular elliptic components at `p₁` and at `p₂`;
2. `f'¹` vanishes on every `G'(𝔸_F)¹`-conjugate of every rational point `r'` of `G'` with
   `P'(r')` not separable;
3. for every rational regular elliptic `r` of `G` and every rational `r'` of `G'` with
   `P(r) = P'(r')`, for all right-invariant Radon measures `μC`, `μD` on the centralizers of
   `r` in `G(𝔸_F)¹` and of `r'` in `G'(𝔸_F)¹` that give the rational points of the two
   centralizers the same covolume, the orbital integrals of `f¹` at `r` and of `f'¹` at `r'`
   agree (quotient measures compatible with `Measure.haar` on the norm-one groups and with
   `μC`, `μD`; covolumes for the counting measures on the rational centralizers);
4. for every rational regular elliptic `r` of `G` such that `P(r)` is the reduced
   characteristic polynomial of no element of `A`, the orbital integrals of `f¹` at `r`
   vanish.

Then `f'` and `f` are integrable, `R'(f') = canonicalIntegratedAction` is trace class on
`L²([G'])`, `R_disc(f) = canonicalDiscreteIntegratedAction` is trace class on `L²_disc([G])`,
and `tr R'(f') = tr R_disc(f)`. -/
def DivisionAlgebraSimpleTraceComparisonStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (A : Type) [DivisionRing A] [Algebra F A]
    [FiniteDimensional F A] [Algebra.IsCentral F A] (n : ℕ),
    Module.finrank F A = n ^ 2 →
    ∀ (hD : IsConnectedReductive Gₐ) (hG : IsConnectedReductive GLₙ)
      (p₁ p₂ : Langlands.Global.FinitePlace F), p₁ ≠ p₂ →
    ∀ (f' : AdelicGroupPoints F Gₐ → ℂ) (f : AdelicGroupPoints F GLₙ → ℂ),
      IsAdelicTestFunction F Gₐ f' → IsAdelicTestFunction F GLₙ f →
    let f'One : normOneSubgroup F Gₐ → ℂ := canonicalNormOneAverage F Gₐ hD f'
    let fOne : normOneSubgroup F GLₙ → ℂ := canonicalNormOneAverage F GLₙ hG f
    let P : RationalGroupPoints F GLₙ → Polynomial F := fun r =>
      ((GeneralLinearGroupPoints.rationalEquiv F n r : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F).charpoly
    let P' : RationalGroupPoints F Gₐ → Polynomial F := fun r' =>
      reducedCharpoly F A (finiteAlgebraRationalUnit r' : A)
    (∀ g ∈ tsupport f,
      IsRegularElliptic (FiniteAdelicGL.localProjection F n p₁
        (AdelicGL.finite F n (GeneralLinearGroupPoints.adelicHomeomorph F n g))) ∧
      IsRegularElliptic (FiniteAdelicGL.localProjection F n p₂
        (AdelicGL.finite F n (GeneralLinearGroupPoints.adelicHomeomorph F n g)))) →
    (∀ r' : RationalGroupPoints F Gₐ, ¬ (P' r').Separable →
      ∀ x : normOneSubgroup F Gₐ, f'One (x⁻¹ * rationalNormOne F Gₐ r' * x) = 0) →
    (∀ (r : RationalGroupPoints F GLₙ) (r' : RationalGroupPoints F Gₐ),
      IsRegularElliptic (GeneralLinearGroupPoints.rationalEquiv F n r) → P r = P' r' →
      let q : normOneSubgroup F GLₙ := rationalNormOne F GLₙ r
      let q' : normOneSubgroup F Gₐ := rationalNormOne F Gₐ r'
      ∀ [MeasurableSpace (LeftQuotient
            (twistedCentralizer (MonoidHom.id (normOneSubgroup F GLₙ)) q))]
        [BorelSpace (LeftQuotient
            (twistedCentralizer (MonoidHom.id (normOneSubgroup F GLₙ)) q))]
        [MeasurableSpace (LeftQuotient ((rationalNormOneSubgroup F GLₙ).subgroupOf
            (twistedCentralizer (MonoidHom.id (normOneSubgroup F GLₙ)) q)))]
        [BorelSpace (LeftQuotient ((rationalNormOneSubgroup F GLₙ).subgroupOf
            (twistedCentralizer (MonoidHom.id (normOneSubgroup F GLₙ)) q)))]
        [MeasurableSpace (LeftQuotient
            (twistedCentralizer (MonoidHom.id (normOneSubgroup F Gₐ)) q'))]
        [BorelSpace (LeftQuotient
            (twistedCentralizer (MonoidHom.id (normOneSubgroup F Gₐ)) q'))]
        [MeasurableSpace (LeftQuotient ((rationalNormOneSubgroup F Gₐ).subgroupOf
            (twistedCentralizer (MonoidHom.id (normOneSubgroup F Gₐ)) q')))]
        [BorelSpace (LeftQuotient ((rationalNormOneSubgroup F Gₐ).subgroupOf
            (twistedCentralizer (MonoidHom.id (normOneSubgroup F Gₐ)) q')))]
        (μC : Measure (twistedCentralizer (MonoidHom.id (normOneSubgroup F GLₙ)) q))
        [μC.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μC] [μC.IsOpenPosMeasure]
        (μD : Measure (twistedCentralizer (MonoidHom.id (normOneSubgroup F Gₐ)) q'))
        [μD.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μD] [μD.IsOpenPosMeasure]
        (νC : Measure (LeftQuotient
          (twistedCentralizer (MonoidHom.id (normOneSubgroup F GLₙ)) q)))
        (νR : Measure (LeftQuotient ((rationalNormOneSubgroup F GLₙ).subgroupOf
          (twistedCentralizer (MonoidHom.id (normOneSubgroup F GLₙ)) q))))
        (νD : Measure (LeftQuotient
          (twistedCentralizer (MonoidHom.id (normOneSubgroup F Gₐ)) q')))
        (νRD : Measure (LeftQuotient ((rationalNormOneSubgroup F Gₐ).subgroupOf
          (twistedCentralizer (MonoidHom.id (normOneSubgroup F Gₐ)) q')))),
        IsCompatible (twistedCentralizer (MonoidHom.id (normOneSubgroup F GLₙ)) q)
          (Measure.haar : Measure (normOneSubgroup F GLₙ)) μC νC →
        IsCompatible ((rationalNormOneSubgroup F GLₙ).subgroupOf
          (twistedCentralizer (MonoidHom.id (normOneSubgroup F GLₙ)) q)) μC Measure.count νR →
        IsCompatible (twistedCentralizer (MonoidHom.id (normOneSubgroup F Gₐ)) q')
          (Measure.haar : Measure (normOneSubgroup F Gₐ)) μD νD →
        IsCompatible ((rationalNormOneSubgroup F Gₐ).subgroupOf
          (twistedCentralizer (MonoidHom.id (normOneSubgroup F Gₐ)) q')) μD Measure.count νRD →
        νR Set.univ = νRD Set.univ →
        orbitalIntegral q νC fOne = orbitalIntegral q' νD f'One) →
    (∀ r : RationalGroupPoints F GLₙ,
      IsRegularElliptic (GeneralLinearGroupPoints.rationalEquiv F n r) →
      (∀ a : A, reducedCharpoly F A a ≠ P r) →
      let q : normOneSubgroup F GLₙ := rationalNormOne F GLₙ r
      ∀ [MeasurableSpace (LeftQuotient
            (twistedCentralizer (MonoidHom.id (normOneSubgroup F GLₙ)) q))]
        [BorelSpace (LeftQuotient
            (twistedCentralizer (MonoidHom.id (normOneSubgroup F GLₙ)) q))]
        (μC : Measure (twistedCentralizer (MonoidHom.id (normOneSubgroup F GLₙ)) q))
        [μC.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μC] [μC.IsOpenPosMeasure]
        (νC : Measure (LeftQuotient
          (twistedCentralizer (MonoidHom.id (normOneSubgroup F GLₙ)) q))),
        IsCompatible (twistedCentralizer (MonoidHom.id (normOneSubgroup F GLₙ)) q)
          (Measure.haar : Measure (normOneSubgroup F GLₙ)) μC νC →
        orbitalIntegral q νC fOne = 0) →
    ∃ (hf' : Integrable f' (Measure.haar : Measure (AdelicGroupPoints F Gₐ)))
      (hf : Integrable f (Measure.haar : Measure (AdelicGroupPoints F GLₙ))),
      IsTraceClass (canonicalIntegratedAction F Gₐ hD f' hf') ∧
      IsTraceClass (canonicalDiscreteIntegratedAction F GLₙ hG f hf) ∧
      operatorTrace (canonicalIntegratedAction F Gₐ hD f' hf') =
        operatorTrace (canonicalDiscreteIntegratedAction F GLₙ hG f hf)

end Langlands.TraceFormula
