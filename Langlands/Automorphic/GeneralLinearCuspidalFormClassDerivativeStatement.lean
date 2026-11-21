import Langlands.Automorphic.GeneralLinearCuspidalSummandRealizationStatement
import Langlands.Automorphic.ConjugateContragredient
import Langlands.Global.ArchimedeanEnvelopingInvariantCenter

/-! # The `L²` classes of cusp forms are differentiable along archimedean exponential curves

For a vector `f` of a cuspidal operator realization of `GL_{r+1}` and a real archimedean Lie
algebra element `X`, the curve `t ↦ πc(exp tX) φ`, where `φ` is the `L²` class of the function
of `f` on the positive-central rational quotient, is differentiable at `t = 0` with derivative
the `L²` class of the function of `X f`. This is the comparison of the genuine differential
action on forms with the derived action of the right regular representation on `L²`, used in
Getz–Hahn, Theorems 6.6.4 and 9.7.3. The statement contains no proof. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme

local instance formClassDerivativeGeneralLinearIsAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance formClassDerivativeGeneralLinearSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

/-- **The `L²` class of a cusp form is differentiable along archimedean exponential curves,
with derivative the class of its Lie derivative** (derived from Getz–Hahn, Theorems 6.6.4 and
9.7.3, with Theorem 9.7.1). With the data of `GeneralLinearCuspidalSummandRealizationStatement`,
let `R` be a cuspidal operator realization of rank `r + 1`, `X` an element of the real Lie
algebra of `GL_{r+1}(F ⊗ ℝ)` and `f` a vector of `R`. If `φ` is the `L²` class of the function
of `f` and `ψ` that of the function of `X f` on the quotient, then the curve
`t ↦ πc(exp(t X)) φ` in the full almost-everywhere cuspidal subspace has derivative `ψ` at
`t = 0`; here `exp(t X)` is the archimedean exponential curve `realLieExponentialCurve`,
placed in the adelic points of the general linear group scheme. -/
def GeneralLinearCuspidalFormClassDerivativeStatement : Prop :=
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
    ∀ (R : Langlands.Automorphic.CuspidalOperatorRealization F r)
      (X : ArchimedeanGL.RealLieAlgebra F (r + 1)) (f : R.Space) (φ ψ : S),
      IsGeneralLinearFormClass F r T i (φ : Lp ℂ 2 _) (R.realization.toContinuous f) →
      IsGeneralLinearFormClass F r T i (ψ : Lp ℂ 2 _)
        (R.realization.toContinuous (R.realization.lieAction X f)) →
      HasDerivAt
        (fun t : ℝ => πc ((GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).symm
          (AdelicGL.ofInfinite F (r + 1) (ArchimedeanGL.realLieExponentialCurve F (r + 1) X t))) φ)
        ψ 0

end Langlands.Automorphic.GroupSchemeFunctions
