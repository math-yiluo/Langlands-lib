import Langlands.GroupScheme.IntegralModelReduction
import Langlands.Geometry.Building.KPZeroSubgroups

/-! # Connected models of torus Iwahori subgroups over the unramified integers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

/-- **KP Proposition B.8.4(3) and Corollary B.8.7 over the maximal
unramified extension.** For any torus over `K = inertiaFixedField F` and
any supplied finite Galois splitting field inside `SeparableClosure F`,
its norm-defined Iwahori subgroup is the integral-point image of a smooth
affine model over `fixedFieldIntegers F` with geometrically connected fibres. -/
def UnramifiedTorusIwahoriModelStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffine T.X.left]
    (L : IntermediateField (inertiaFixedField F) (SeparableClosure F))
    [FiniteDimensional (inertiaFixedField F) L] [IsGalois (inertiaFixedField F) L],
    IsSplitTorus (baseChanged (inertiaFixedField F) L T.toGrp) →
    ∃ M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) T.toGrp,
      M.IsSmooth ∧ M.HasGeometricallyConnectedFibres ∧
        M.integralPoints =
          torusNormIwahori (inertiaFixedField F) L (intermediateValuation F L) T

end Langlands.BruhatTits.IntegralModels
