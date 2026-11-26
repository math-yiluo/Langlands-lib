import Langlands.Automorphic.GroupSchemeFullAEL2Integrated
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
import Langlands.BaseChange.OrbitalIntegral
import Langlands.JacquetLanglands.RegularElliptic

/-!
# Global matching of orbital integrals from local concordance, for cyclic base change of `GL_n`

Let `L/K` be a cyclic extension of number fields of degree `l` whose Galois group is generated
by `σ`, let `W = Res_{L/K} GL_n` with the automorphism `θ` attached to `σ`, and let `G = GL_n`
over `K`.  Let `S` be a finite set of places of `K` containing the infinite places, and let
`φ` on `W(𝔸_K)` and `f` on `G(𝔸_K)` be restricted tensor products of continuous compactly
supported local functions `φ_i` on `W(K_i) = GL_n(K_i ⊗_K L)` and `f_i` on `GL_n(K_i)` at the
places `i ∈ S` and of the characteristic functions of `GL_n(O_{E_v})` and `GL_n(O_v)` at the
finite places `v ∉ S`.  Suppose that `φ_i` and `f_i` are concordant (Henniart–Lemaire I.2.5)
for fixed Haar measures at every `i ∈ S`, and that the two characteristic functions are
concordant for the Haar measures giving them volume one at every finite `v ∉ S` (the
fundamental lemma for the unit elements).  Then there is a real constant `c > 0`, chosen
before the local functions and depending only on the fields, `n`, the central torus, `S` and
the local Haar measures at the places of `S`, such that the two global hypotheses of
`GeneralLinearBaseChangeTraceComparisonStatement` hold for `φ` and `f` with this `c`:
matching of the twisted and ordinary orbital integrals on the norm-one groups at rational norm
pairs, and vanishing of the ordinary orbital integrals at rational elements that are not norms.

This is the local-to-global step of Arthur–Clozel 1989, Chapter 1, §4 (printed pp. 42–44), and
of Henniart–Lemaire 2011, II.6.6 (printed pp. 122–123).  See
`GeneralLinearBaseChangeGlobalMatchingStatement.md`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.QuotientIntegration Langlands.JacquetLanglands
open Langlands.TraceFormula.AdelicGroupAutomorphism
open Langlands.BaseChange

namespace Langlands.TraceFormula

open scoped Langlands.TraceFormula.PlaceCompletion

local instance generalLinearBaseChangeMatchingIsAffine (K : Type u) [Field K] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

local instance generalLinearBaseChangeMatchingSmooth (K : Type u) [Field K] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

/-- The Borel σ-algebra on `GL_n(K_i)`. -/
local instance generalLinearBaseChangeMatchingPlaceMeasurable (K : Type u) [Field K]
    [NumberField K] (n : ℕ) (i : Place K) :
    MeasurableSpace (GeneralLinear n (placeCompletion K i)) :=
  borel _

local instance generalLinearBaseChangeMatchingPlaceBorel (K : Type u) [Field K]
    [NumberField K] (n : ℕ) (i : Place K) :
    BorelSpace (GeneralLinear n (placeCompletion K i)) :=
  ⟨rfl⟩

/-- The Borel σ-algebra on `GL_n(E_i)`, `E_i = K_i ⊗_K L`. -/
local instance generalLinearBaseChangeMatchingLocalMeasurable (K : Type u) [Field K]
    [NumberField K] (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] (n : ℕ)
    (i : Place K) :
    MeasurableSpace (GeneralLinear n (LocalBaseChangeAlgebra K L i)) :=
  borel _

local instance generalLinearBaseChangeMatchingLocalBorel (K : Type u) [Field K]
    [NumberField K] (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] (n : ℕ)
    (i : Place K) :
    BorelSpace (GeneralLinear n (LocalBaseChangeAlgebra K L i)) :=
  ⟨rfl⟩

set_option hygiene false in
/-- The `GL_n` group scheme over `K`, for the bound variables `K` and `n`. -/
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

set_option hygiene false in
/-- The Weil restriction `Res_{L/K} GL_n`, for the bound variables `K`, `L` and `n`. -/
local notation "Wₙ" => weilGroup K L GLₙ

/-- Global matching of orbital integrals for cyclic base change of `GL_n`, from local
concordance at a finite set of places and the fundamental lemma for the unit elements
elsewhere.

Let `L/K` be a cyclic extension of number fields with `IsCyclicAlgebra σ l`, and let `T₀` be a
commutative group scheme over `K` with an isomorphism `e₀` onto a split torus, with central
morphisms `iG : T₀ → GL_n` and `iW : T₀ → W = Res_{L/K} GL_n`, both injective on rational
characters with image of finite index, such that `iW = iG ≫ unit` for the unit
`unit : GL_n → W` of the Weil restriction.  Assume that the Haar measures of `W(𝔸_K)¹` and
`G(𝔸_K)¹` are right invariant.  Let `S` be a finite set of places of `K` containing the
infinite places, and let `μF i`, `μE i` be measures on `GL_n(K_i)` and `GL_n(E_i)`,
`E_i = K_i ⊗_K L`, that are Haar measures for `i ∈ S`.  Suppose that at every finite place
`v ∉ S`, the characteristic functions of `GL_n(O_{E_v})` and `GL_n(O_v)` are concordant for
every pair of Haar measures giving these two subgroups volume one.  Then there is a real
`c > 0` such that for all local functions `φ_i` on `GL_n(E_i)` and `f_i` on `GL_n(K_i)` that
are continuous with compact support and concordant for `μF i` and `μE i` at every `i ∈ S`,
for all `φ` on `W(𝔸_K)` and `f` on `GL_n(𝔸_K)` that are the restricted tensor products of
these functions at the places of `S` and of the characteristic functions of the integral
subgroups outside `S`, with averages `φ¹` and `f¹` over the positive real points of `T₀`, and
for every finite place `w` of `L` and `v` of `K`:
* for all rational norm-one points `r` of `W` and `q` of `G` and every `y ∈ GL_n(L)` with
  `Φ(N(r)) y = y ΦG(q)`, where `Φ(N(r))` is regular elliptic at `w` or `q` is regular elliptic
  at `v`, every isomorphism `e` from the `θ`-centralizer of `r` in `W(𝔸_K)¹` onto the
  centralizer of `q` in `G(𝔸_K)¹` with `ΦG(e(x)) = y⁻¹ Φ(x) y`, every right-invariant measure
  `μr` on the first that is finite on compacts and positive on nonempty open sets, every
  right-invariant `μq = e_* μr` on the second, and all compatible quotient measures `νr` and
  `νq`, the twisted orbital integral of `φ¹` at `r` for `νr` equals `c` times the orbital
  integral of `f¹` at `q` for `νq`;
* for every rational norm-one point `q` of `G` regular elliptic at `v` such that no `Φ(N(r))`
  with `r` a rational norm-one point of `W` is conjugate to `ΦG(q)` by an element of
  `GL_n(L)`, the orbital integral of `f¹` at `q` vanishes for every right-invariant measure on
  its centralizer that is finite on compacts and positive on nonempty open sets and every
  compatible quotient measure.

These two conclusions are, verbatim, the two hypotheses of
`GeneralLinearBaseChangeTraceComparisonStatement` on the orbital integrals, for
`TW = TG = T₀`, `IW = IG = I` and `eW = eG = e₀`. -/
def GeneralLinearBaseChangeGlobalMatchingStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (L : Type u) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (l : ℕ), IsCyclicAlgebra σ l →
    ∀ (n : ℕ) (T₀ : CommGroupScheme (Spec (CommRingCat.of K)))
    (iG : T₀.toGrp ⟶ GLₙ) (hiG : Function.Injective (characterRestrict iG))
    [(characterRestrict iG).range.FiniteIndex]
    (iW : T₀.toGrp ⟶ Wₙ) (hiW : Function.Injective (characterRestrict iW))
    [(characterRestrict iW).range.FiniteIndex]
    (I : Type u) [Fintype I] (e₀ : T₀.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I)
    (hcG : IsCentral iG) (hcW : IsCentral iW)
    [(Measure.haar : Measure (normOneSubgroup K Wₙ)).IsMulRightInvariant]
    [(Measure.haar : Measure (normOneSubgroup K GLₙ)).IsMulRightInvariant],
    iW = iG ≫ AffineWeil.unit K L GLₙ →
    ∀ (S : Finset (Place K)), (∀ w : Langlands.Global.InfinitePlace K, (Sum.inl w : Place K) ∈ S) →
    ∀ (μF : (i : Place K) → Measure (GeneralLinear n (placeCompletion K i)))
      (μE : (i : Place K) → Measure (GeneralLinear n (LocalBaseChangeAlgebra K L i))),
      (∀ i ∈ S, (μF i).IsHaarMeasure ∧ (μE i).IsHaarMeasure) →
      (∀ v : Langlands.Global.FinitePlace K, (Sum.inr v : Place K) ∉ S →
        ∀ (μFv : Measure (GeneralLinear n (placeCompletion K (.inr v))))
          (μEv : Measure (GeneralLinear n (LocalBaseChangeAlgebra K L (.inr v)))),
          μFv.IsHaarMeasure → μEv.IsHaarMeasure →
          μFv (Langlands.GeneralLinearGroup.integralSubgroup (Fin n)
            (show Subring (placeCompletion K (.inr v)) from
              (v.adicCompletionIntegers K).toSubring)) = 1 →
          μEv (Langlands.GeneralLinearGroup.integralSubgroup (Fin n)
            (localIntegers K L v)) = 1 →
          AreConcordant (localGalois K L σ (.inr v)) l μFv μEv
            ((Langlands.GeneralLinearGroup.integralSubgroup (Fin n) (localIntegers K L v) :
              Set (GeneralLinear n (LocalBaseChangeAlgebra K L (.inr v)))).indicator 1)
            ((Langlands.GeneralLinearGroup.integralSubgroup (Fin n)
              (show Subring (placeCompletion K (.inr v)) from
                (v.adicCompletionIntegers K).toSubring) :
              Set (GeneralLinear n (placeCompletion K (.inr v)))).indicator 1)) →
    let Φ : AdelicGroupPoints K Wₙ → AdelicGL L n := fun g =>
      GeneralLinearGroupPoints.adelicHomeomorph L n
        (AdelicGroupPoints.map L (AffineWeil.unitBaseChange K L GLₙ)
          (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of L))
          (GroupScheme.GeneralLinear.baseChangeIso (Fin n) (Spec.algebraMap K L)).hom
          (AdelicGaloisUnit.weilAdelicEquiv K L GLₙ g))
    let N : AdelicGroupPoints K Wₙ → AdelicGroupPoints K Wₙ := fun g =>
      ((List.range l).map fun k => adelicAut K (unitGaloisAut K L GLₙ σ ^ k) g).prod
    let θ : normOneSubgroup K Wₙ ≃ₜ* normOneSubgroup K Wₙ :=
      normOneAut K (unitGaloisAut K L GLₙ σ)
    let incl : AdelicGL K n →* AdelicGL L n :=
      Matrix.GeneralLinearGroup.map (AdelicFunctoriality.adeleInclusion (K := K) (L := L))
    let ΦG : AdelicGroupPoints K GLₙ → AdelicGL L n := fun g =>
      incl (GeneralLinearGroupPoints.adelicHomeomorph K n g)
    ∃ c : ℝ, 0 < c ∧
    ∀ (φloc : (i : Place K) → GeneralLinear n (LocalBaseChangeAlgebra K L i) → ℂ)
      (floc : (i : Place K) → GeneralLinear n (placeCompletion K i) → ℂ),
      (∀ i ∈ S, Continuous (φloc i) ∧ HasCompactSupport (φloc i)) →
      (∀ i ∈ S, Continuous (floc i) ∧ HasCompactSupport (floc i)) →
      (∀ i ∈ S, AreConcordant (localGalois K L σ i) l (μF i) (μE i) (φloc i) (floc i)) →
    ∀ (φ : AdelicGroupPoints K Wₙ → ℂ) (f : AdelicGroupPoints K GLₙ → ℂ),
      IsAdelicFactorization K S (fun i p => φloc i (localPointsEquiv K L n i p))
        (localIntegralFamily K L n) φ →
      IsAdelicFactorization K S (fun i p => floc i (localGLEquiv K n i p))
        (glIntegralFamily K n) f →
    let φOne : normOneSubgroup K Wₙ → ℂ := fun x =>
      ∫ a, φ (positivePointMap K Wₙ T₀ iW a * x)
        ∂normalizedPositiveHaarMeasure K Wₙ T₀ iW hiW I e₀ hcW
    let fOne : normOneSubgroup K GLₙ → ℂ := fun x =>
      ∫ a, f (positivePointMap K GLₙ T₀ iG a * x)
        ∂normalizedPositiveHaarMeasure K GLₙ T₀ iG hiG I e₀ hcG
    ∀ (w : Langlands.Global.FinitePlace L) (v : Langlands.Global.FinitePlace K),
      (∀ r ∈ rationalNormOneSubgroup K Wₙ, ∀ q ∈ rationalNormOneSubgroup K GLₙ,
        ∀ y : GL (Fin n) L,
        Φ (N (r : AdelicGroupPoints K Wₙ)) * AdelicGL.rational L n y =
            AdelicGL.rational L n y * ΦG (q : AdelicGroupPoints K GLₙ) →
        (IsRegularElliptic (FiniteAdelicGL.localProjection L n w
            (AdelicGL.finite L n (Φ (N (r : AdelicGroupPoints K Wₙ))))) ∨
          IsRegularElliptic (FiniteAdelicGL.localProjection K n v
            (AdelicGL.finite K n (GeneralLinearGroupPoints.adelicHomeomorph K n
              (q : AdelicGroupPoints K GLₙ))))) →
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
          twistedOrbitalIntegral θ r νr φOne = (c : ℂ) * orbitalIntegral q νq fOne) ∧
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
          orbitalIntegral q νq fOne = 0)

end Langlands.TraceFormula
