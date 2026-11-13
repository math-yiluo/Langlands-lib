import Langlands.GroupScheme.IntegralModelReduction
import Langlands.Geometry.Building.KPZeroSubgroups

/-! # The torus Iwahori subgroup as an image of a connected smooth model -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

/-- **KP Lemma B.3.1 and Definition 2.5.13 over the maximal unramified
extension.** For a torus `T` over `K = inertiaFixedField F` split by a finite
Galois intermediate field `L` of `SeparableClosure F / K`, the norm-defined
Iwahori subgroup `T(K)^0` is the image, under some homomorphism of `K`-groups
`n : S ⟶ T`, of the integral points of a smooth model of `S` over
`fixedFieldIntegers F` with geometrically connected fibres. In the source
`S = R_{L/K}(T_L)`, its model is the Weil restriction of the split torus over
the integers of `L`, and `n` is the norm. -/
def UnramifiedTorusIwahoriConnectedImageStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffine T.X.left]
    (L : IntermediateField (inertiaFixedField F) (SeparableClosure F))
    [FiniteDimensional (inertiaFixedField F) L] [IsGalois (inertiaFixedField F) L],
    IsSplitTorus (baseChanged (inertiaFixedField F) L T.toGrp) →
    ∃ (S : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
      (W : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) S) (n : S ⟶ T.toGrp),
      W.IsSmooth ∧ W.HasGeometricallyConnectedFibres ∧
        W.integralPoints.map (rationalPoints.map n) =
          torusNormIwahori (inertiaFixedField F) L (intermediateValuation F L) T

end Langlands.BruhatTits.IntegralModels
