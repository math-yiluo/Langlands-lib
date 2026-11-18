import Langlands.Automorphic.GeneralLinearCuspidalMultiplicityOneStatement
import Langlands.Automorphic.CuspidalOperatorRealization

/-! # Irreducible cuspidal `L²` summands of `GL_n` and cuspidal operator realizations

Getz–Hahn, Theorem 9.7.3 (with Theorem 9.7.1 and Lemma 9.7.2): the `K`-finite vectors of a
discrete cuspidal automorphic representation `V ≤ L²_cusp([GL_n])` are cusp forms and form a
cuspidal automorphic representation, dense in `V`, and every cuspidal automorphic
representation arises in this way. This module states the two directions of this
correspondence between the Library's full almost-everywhere cuspidal subspace of `L²` of the
positive-central rational quotient `[GL_n]` and the Library's cuspidal operator realizations
`CuspidalOperatorRealization F r` (forms on `GL_{r+1}(𝔸_F)` in the matrix model).

A vector of a realization is attached to the `L²` class of the function it induces on the
quotient (`IsGeneralLinearFormClass`). The forms follow the Library's Borel–Jacquet conventions
(finite-level smooth functions with a growth bound on each finite slice); the paired Markdown
compares them with Getz–Hahn's definitions. The statements contain no proof. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme

local instance summandRealizationGeneralLinearIsAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance summandRealizationGeneralLinearSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

/-- The `L²` class `φ` on the positive-central rational quotient of `GL_{r+1}` is the class of
the matrix-model continuous function `f` on `GL_{r+1}(𝔸_F)`: there is a continuous function `h`
on the quotient whose pullback to the adelic points, transported to the matrix model by
`continuousGeneralLinearEquiv`, is `f`, and `φ` agrees with `h` almost everywhere for the
quotient Haar measure. -/
def IsGeneralLinearFormClass (F : Type u) [Field F] [NumberField F] (r : ℕ)
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : T.toGrp ⟶ GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))
    (φ : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)) T i))
    (f : Langlands.Automorphic.ContinuousRationalFunctions F (r + 1)) : Prop :=
  ∃ h : C(PositiveRationalQuotient F
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)) T i, ℂ),
    continuousGeneralLinearEquiv F (r + 1)
        (positiveQuotientContinuousPullback F _ T i h) = f ∧
      (φ : PositiveRationalQuotient F
          (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)) T i → ℂ)
        =ᵐ[positiveRationalQuotientHaarMeasure F _ T i] h

/-- **Irreducible cuspidal `L²` summands come from cuspidal operator realizations**
(Getz–Hahn, Theorem 9.7.3, with Theorem 9.7.1 and Lemma 9.7.2). Let `F` be a number field whose
adele quotient is compact, let `T → GL_{r+1}` be a central split torus with injective character
restriction of finite-index image (for example the centre `G_m`), and let `S` be the full
almost-everywhere cuspidal subspace of `L²([GL_{r+1}])` with its right regular action `πc`.
For every nonzero closed invariant subspace `P` of `S` with no closed invariant subspaces other
than `0` and itself, there are a cuspidal operator realization `R` of rank `r + 1` and a linear
map `Φ` from its space to `S` which sends every vector to the `L²` class of the function it
induces on the quotient, such that the closure of the image of `Φ` is `P`. -/
def GeneralLinearCuspidalSummandRealizationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (hPD : ParabolicDynamicStatement.{u})
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : T.toGrp ⟶ GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))).IsMulRightInvariant],
    let hG := GroupScheme.isConnectedReductive_generalLinear F (Fin (r + 1))
    let S := fullAEL2CuspidalSubmodule F _ hPD hG T i hi I e hc
    let πc := fullAEL2CuspidalBoundedRightAction F _ hPD hG T i hi I e hc
    ∀ P : Submodule ℂ S,
      (P ≠ ⊥ ∧ IsClosed (P : Set S) ∧ (∀ a, ∀ x ∈ P, πc a x ∈ P) ∧
        ∀ P' : Submodule ℂ S, P' ≤ P → IsClosed (P' : Set S) →
          (∀ a, ∀ x ∈ P', πc a x ∈ P') → P' = ⊥ ∨ P' = P) →
      ∃ (R : Langlands.Automorphic.CuspidalOperatorRealization F r) (Φ : R.Space →ₗ[ℂ] S),
        (∀ f : R.Space,
          IsGeneralLinearFormClass F r T i (Φ f : Lp ℂ 2 _) (R.realization.toContinuous f)) ∧
        (LinearMap.range Φ).topologicalClosure = P

/-- **Cuspidal operator realizations with positive-central invariance give irreducible cuspidal
`L²` summands** (Getz–Hahn, Theorem 9.7.3, with Theorem 9.7.1). With the data of
`GeneralLinearCuspidalSummandRealizationStatement`, let `R` be a cuspidal operator realization
of rank `r + 1` each of whose vectors induces a continuous function on the positive-central
rational quotient (that is, is invariant under the positive image of `T`). Then there are a
nonzero closed invariant subspace `P` of `S` with no closed invariant subspaces other than `0`
and itself, and a linear map `Φ` from the space of `R` to `S` which sends every vector to the
`L²` class of the function it induces on the quotient, such that the closure of the image of
`Φ` is `P`. -/
def GeneralLinearCuspidalRealizationSummandStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (hPD : ParabolicDynamicStatement.{u})
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : T.toGrp ⟶ GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))).IsMulRightInvariant],
    let hG := GroupScheme.isConnectedReductive_generalLinear F (Fin (r + 1))
    let S := fullAEL2CuspidalSubmodule F _ hPD hG T i hi I e hc
    let πc := fullAEL2CuspidalBoundedRightAction F _ hPD hG T i hi I e hc
    ∀ R : Langlands.Automorphic.CuspidalOperatorRealization F r,
      (∀ f : R.Space, ∃ h : C(PositiveRationalQuotient F
          (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)) T i, ℂ),
        continuousGeneralLinearEquiv F (r + 1)
          (positiveQuotientContinuousPullback F _ T i h) = R.realization.toContinuous f) →
      ∃ (P : Submodule ℂ S) (Φ : R.Space →ₗ[ℂ] S),
        (P ≠ ⊥ ∧ IsClosed (P : Set S) ∧ (∀ a, ∀ x ∈ P, πc a x ∈ P) ∧
          ∀ P' : Submodule ℂ S, P' ≤ P → IsClosed (P' : Set S) →
            (∀ a, ∀ x ∈ P', πc a x ∈ P') → P' = ⊥ ∨ P' = P) ∧
        (∀ f : R.Space,
          IsGeneralLinearFormClass F r T i (Φ f : Lp ℂ 2 _) (R.realization.toContinuous f)) ∧
        (LinearMap.range Φ).topologicalClosure = P

end Langlands.Automorphic.GroupSchemeFunctions
