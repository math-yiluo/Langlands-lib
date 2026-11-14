import Langlands.Geometry.Building.Kottwitz.TorusMap
import Langlands.Geometry.Building.KPZeroSubgroups

/-! # The character kernel of the torus Kottwitz map -/

noncomputable section

universe u

open AlgebraicGeometry
open Langlands.GroupScheme
open Langlands.GroupScheme.GaloisPointComparison
open scoped CategoryTheory.MonObj

namespace Langlands.Geometry.Building.Kottwitz

/-- KP Lemma 11.1.3 and its rational-point restriction: the torus character
kernel is the preimage of inertia torsion under the constructed map. -/
def TorusCharacterKernelStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (hT : IsTorus T.toGrp),
    characterValuationKernel (ValuativeRel.valuation F) T.toGrp =
      (CommGroup.torsion (Multiplicative (TorusTarget F F T))).comap
        ((torusKottwitz F F T hT).comp
          ((GaloisPoint.extend F (UnramifiedClosure F) T.toGrp).comp
            (rationalCoeffEquiv F T.toGrp).toMonoidHom))

end Langlands.Geometry.Building.Kottwitz
