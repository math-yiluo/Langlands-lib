import Langlands.GroupScheme.IntegralModelReduction
import Langlands.Geometry.Building.KPZeroSubgroups

/-! # Integral points of connected torus models lie in the Iwahori subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

/-- **KP Corollary B.8.7 with the argument of Proposition B.8.8(3), over the
maximal unramified extension.** For a torus `T` over `K = inertiaFixedField F`
split by a finite Galois intermediate field `L` of `SeparableClosure F / K`,
every smooth model of `T` over `fixedFieldIntegers F` with geometrically
connected fibres has its integral-point image inside the norm-defined Iwahori
subgroup `T(K)^0`. -/
def UnramifiedTorusConnectedBoundStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffine T.X.left]
    (L : IntermediateField (inertiaFixedField F) (SeparableClosure F))
    [FiniteDimensional (inertiaFixedField F) L] [IsGalois (inertiaFixedField F) L],
    IsSplitTorus (baseChanged (inertiaFixedField F) L T.toGrp) →
    ∀ M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) T.toGrp,
      M.IsSmooth → M.HasGeometricallyConnectedFibres →
        M.integralPoints ≤
          torusNormIwahori (inertiaFixedField F) L (intermediateValuation F L) T

end Langlands.BruhatTits.IntegralModels
