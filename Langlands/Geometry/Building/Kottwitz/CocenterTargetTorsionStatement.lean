import Langlands.Geometry.Building.Kottwitz.ReductiveMap

/-! # Torsion in the kernel of the cocenter inertia map -/

noncomputable section

universe u

open AlgebraicGeometry
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.Geometry.Building.Kottwitz

/-- The cocenter map on inertia targets has torsion kernel, as needed in the
proof of KP Lemma 11.5.2. -/
def CocenterTargetTorsionStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (c : Cocenter F G),
    (cocenterTargetMap F F G hG c).toAddMonoidHom.toMultiplicative.ker ≤
      fundamentalInertiaTorsion F (UnramifiedClosure F) (SeparableClosure F) G hG

end Langlands.Geometry.Building.Kottwitz
