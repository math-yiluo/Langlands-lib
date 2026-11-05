import Langlands.GroupScheme.Torus.Induced
import Langlands.Geometry.Building.KPZeroSubgroups

/-! # KP Lemma 2.5.18 over `K` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- KP Lemma 2.5.18 for `k = K`: for an induced `K`-torus `T`, `T(K)^0 = T(K)^1`. -/
def InducedTorusIwahoriStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))) [IsAffine T.X.left]
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    [FiniteDimensional (UnramifiedClosure F) L] [IsGalois (UnramifiedClosure F) L],
    IsSplitTorus (GaloisPointComparison.baseChanged (UnramifiedClosure F) L T.toGrp) →
    IsInducedTorus T →
    torusNormIwahori (UnramifiedClosure F) L (intermediateValuation F L) T =
      characterValuationKernel (LocalGalois.Separable.fixedFieldValuation F) T.toGrp

end Langlands.Geometry.Building
