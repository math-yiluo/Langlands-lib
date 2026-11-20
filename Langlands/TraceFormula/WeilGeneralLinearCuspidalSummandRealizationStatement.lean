import Langlands.Automorphic.GeneralLinearCuspidalSummandRealizationStatement
import Langlands.TraceFormula.GeneralLinearWeilAdelicTwistStatement

/-!
# Irreducible cuspidal `L²` summands of `Res_{L/K} GL_n` and cuspidal realizations over `L`

Let `L/K` be a finite extension of number fields and `W = Res_{L/K} GL_{r+1}` the Library's Weil
restriction (`weilGroup K L GLᵣ₊₁`). The twisted trace formula for `W`
(`GeneralLinearSimpleTwistedTraceFormulaStatement`) acts on the Library's full
almost-everywhere cuspidal subspace of `L²` of the positive-central rational quotient `[W]` of
`W(𝔸_K)`. Cuspidal automorphic representations of `GL_{r+1}(𝔸_L)` are the Library's cuspidal
operator realizations over `L`, in the matrix model. This module states that the two are
matched through the identification `Φ : W(𝔸_K) → GL_{r+1}(𝔸_L)` of
`GeneralLinearWeilAdelicTwistStatement` (built from `weilAdelicEquiv`, the base-change
isomorphism of `GL_{r+1}` and `adelicHomeomorph`), in the form used for `GL_{r+1}` over a single
field by `GeneralLinearCuspidalSummandRealizationStatement`.

An `L²` class on `[W]` is attached to a matrix-model function `f` on `GL_{r+1}(𝔸_L)` when it is
the class of a continuous function on the quotient whose pullback to `W(𝔸_K)` is `f ∘ Φ`
(`IsWeilFormClass`).

The statements contain no proof. The paired Markdown gives the sources and the argument.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.Automorphic.GroupSchemeFunctions
open Langlands.TraceFormula.AdelicGroupAutomorphism

namespace Langlands.TraceFormula

local instance weilSummandRealizationIsAffine (K : Type u) [Field K] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

local instance weilSummandRealizationSmooth (K : Type u) [Field K] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

set_option hygiene false in
/-- The Weil restriction `Res_{L/K} GL_{r+1}`, for the bound variables `K`, `L` and `r`. -/
local notation "Wᵣ" =>
  weilGroup K L (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of K))

/-- The `L²` class `φ` on the positive-central rational quotient of `W = Res_{L/K} GL_{r+1}` is
the class of the matrix-model continuous function `f` on `GL_{r+1}(𝔸_L)`: there is a continuous
function `h` on the quotient whose pullback to `W(𝔸_K)` is `f ∘ Φ`, where
`Φ : W(𝔸_K) → GL_{r+1}(𝔸_L)` is the identification of `GeneralLinearWeilAdelicTwistStatement`,
and `φ` agrees with `h` almost everywhere for the quotient Haar measure. -/
def IsWeilFormClass (K : Type u) [Field K] [NumberField K] (L : Type u) [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] (r : ℕ)
    (T : CommGroupScheme (Spec (CommRingCat.of K))) (i : T.toGrp ⟶ Wᵣ)
    (φ : Lp ℂ 2 (positiveRationalQuotientHaarMeasure K Wᵣ T i))
    (f : Langlands.Automorphic.ContinuousRationalFunctions L (r + 1)) : Prop :=
  let Φ : AdelicGroupPoints K Wᵣ → AdelicGL L (r + 1) := fun g =>
    GeneralLinearGroupPoints.adelicHomeomorph L (r + 1)
      (AdelicGroupPoints.map L
        (AffineWeil.unitBaseChange K L
          (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of K)))
        (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of L))
        (GroupScheme.GeneralLinear.baseChangeIso (Fin (r + 1)) (Spec.algebraMap K L)).hom
        (AdelicGaloisUnit.weilAdelicEquiv K L
          (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of K)) g))
  ∃ h : C(PositiveRationalQuotient K Wᵣ T i, ℂ),
    (∀ g : AdelicGroupPoints K Wᵣ,
      h (LeftCosetSpace.mk (positiveRationalSubgroup K Wᵣ T i) g) =
        Langlands.Automorphic.ContinuousRationalFunctions.evaluate L (r + 1) f (Φ g)) ∧
      (φ : PositiveRationalQuotient K Wᵣ T i → ℂ)
        =ᵐ[positiveRationalQuotientHaarMeasure K Wᵣ T i] h

/-- **Irreducible cuspidal `L²` summands of `Res_{L/K} GL_{r+1}` come from cuspidal operator
realizations over `L`.** Let `L/K` be a finite extension of number fields, the adele quotient of
`L` being compact, `W = Res_{L/K} GL_{r+1}` with a proof `hG` that it is connected reductive, and
`T → W` a central split torus with injective character restriction of finite-index image. Let
`S` be the full almost-everywhere cuspidal subspace of `L²([W])` with its right regular action
`πc`. For every nonzero closed invariant subspace `P` of `S` with no closed invariant subspaces
other than `0` and itself, there are a cuspidal operator realization `R` of `GL_{r+1}` over `L`
and a linear map `Ψ` from its space to `S` sending every vector to the `L²` class of the function
it induces on `[W]` (`IsWeilFormClass`), such that the closure of the image of `Ψ` is `P`. -/
def WeilGeneralLinearCuspidalSummandRealizationStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (L : Type u) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [CompactSpace (AdeleQuotient L)] (r : ℕ)
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive Wᵣ)
    (T : CommGroupScheme (Spec (CommRingCat.of K))) (i : T.toGrp ⟶ Wᵣ)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup K Wᵣ)).IsMulRightInvariant],
    let S := fullAEL2CuspidalSubmodule K Wᵣ hPD hG T i hi I e hc
    let πc := fullAEL2CuspidalBoundedRightAction K Wᵣ hPD hG T i hi I e hc
    ∀ P : Submodule ℂ S,
      (P ≠ ⊥ ∧ IsClosed (P : Set S) ∧ (∀ a, ∀ x ∈ P, πc a x ∈ P) ∧
        ∀ P' : Submodule ℂ S, P' ≤ P → IsClosed (P' : Set S) →
          (∀ a, ∀ x ∈ P', πc a x ∈ P') → P' = ⊥ ∨ P' = P) →
      ∃ (R : Langlands.Automorphic.CuspidalOperatorRealization L r) (Ψ : R.Space →ₗ[ℂ] S),
        (∀ f : R.Space,
          IsWeilFormClass K L r T i (Ψ f : Lp ℂ 2 _) (R.realization.toContinuous f)) ∧
        (LinearMap.range Ψ).topologicalClosure = P

/-- **Cuspidal operator realizations over `L` with positive-central invariance give irreducible
cuspidal `L²` summands of `Res_{L/K} GL_{r+1}`.** With the data of
`WeilGeneralLinearCuspidalSummandRealizationStatement`, let `R` be a cuspidal operator
realization of `GL_{r+1}` over `L` each of whose vectors `f`, composed with
`Φ : W(𝔸_K) → GL_{r+1}(𝔸_L)`, is the pullback of a continuous function on the positive-central
rational quotient `[W]`. Then there are a nonzero closed invariant subspace `P` of `S` with no
closed invariant subspaces other than `0` and itself, and a linear map `Ψ` from the space of `R`
to `S` sending every vector to the `L²` class of the function it induces on `[W]`
(`IsWeilFormClass`), such that the closure of the image of `Ψ` is `P`. -/
def WeilGeneralLinearCuspidalRealizationSummandStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (L : Type u) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [CompactSpace (AdeleQuotient L)] (r : ℕ)
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive Wᵣ)
    (T : CommGroupScheme (Spec (CommRingCat.of K))) (i : T.toGrp ⟶ Wᵣ)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup K Wᵣ)).IsMulRightInvariant],
    let S := fullAEL2CuspidalSubmodule K Wᵣ hPD hG T i hi I e hc
    let πc := fullAEL2CuspidalBoundedRightAction K Wᵣ hPD hG T i hi I e hc
    let Φ : AdelicGroupPoints K Wᵣ → AdelicGL L (r + 1) := fun g =>
      GeneralLinearGroupPoints.adelicHomeomorph L (r + 1)
        (AdelicGroupPoints.map L
          (AffineWeil.unitBaseChange K L
            (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of K)))
          (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of L))
          (GroupScheme.GeneralLinear.baseChangeIso (Fin (r + 1)) (Spec.algebraMap K L)).hom
          (AdelicGaloisUnit.weilAdelicEquiv K L
            (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of K)) g))
    ∀ R : Langlands.Automorphic.CuspidalOperatorRealization L r,
      (∀ f : R.Space, ∃ h : C(PositiveRationalQuotient K Wᵣ T i, ℂ),
        ∀ g : AdelicGroupPoints K Wᵣ,
          h (LeftCosetSpace.mk (positiveRationalSubgroup K Wᵣ T i) g) =
            Langlands.Automorphic.ContinuousRationalFunctions.evaluate L (r + 1)
              (R.realization.toContinuous f) (Φ g)) →
      ∃ (P : Submodule ℂ S) (Ψ : R.Space →ₗ[ℂ] S),
        (P ≠ ⊥ ∧ IsClosed (P : Set S) ∧ (∀ a, ∀ x ∈ P, πc a x ∈ P) ∧
          ∀ P' : Submodule ℂ S, P' ≤ P → IsClosed (P' : Set S) →
            (∀ a, ∀ x ∈ P', πc a x ∈ P') → P' = ⊥ ∨ P' = P) ∧
        (∀ f : R.Space,
          IsWeilFormClass K L r T i (Ψ f : Lp ℂ 2 _) (R.realization.toContinuous f)) ∧
        (LinearMap.range Ψ).topologicalClosure = P

end Langlands.TraceFormula
