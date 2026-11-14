import Langlands.Geometry.Building.Kottwitz.TorusMap
import Langlands.Geometry.Building.Kottwitz.TorusInertiaFunctoriality

/-! # Naturality of torus Kottwitz homomorphisms for actual torus morphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.Kottwitz

/-- Functoriality of the selected torus Kottwitz homomorphisms for every actual morphism of
tori. This is derived from the norm characterization and uniqueness in KP Proposition 11.1.1;
the functoriality is invoked in the proofs of KP Lemmas 11.1.3 and 11.5.1. -/
def TorusKottwitzNaturalityStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (k : Type u) [Field k] [Algebra k (UnramifiedClosure F)]
    [Algebra k (SeparableClosure F)] [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)]
    [Normal k (UnramifiedClosure F)]
    (S T : CommGroupScheme (Spec (CommRingCat.of k)))
    (hS : IsTorus S.toGrp) (hT : IsTorus T.toGrp) (f : S ⟶ T) (x : torusKPoints F k S),
    (torusKottwitz F k T hT
      (affinePointsTarget S.toGrp (CommGroupScheme.groupHom f)
        (CommAlgCat.of k (UnramifiedClosure F)) x)).toAdd =
    torusInertiaMap k (SeparableClosure F) f (UnramifiedClosure F)
      (torusKottwitz F k S hS x).toAdd

end Langlands.Geometry.Building.Kottwitz
