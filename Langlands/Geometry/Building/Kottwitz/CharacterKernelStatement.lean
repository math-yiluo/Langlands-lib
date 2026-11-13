import Langlands.Geometry.Building.Kottwitz.ReductiveMap

/-! # KP Lemma 11.5.2: the character-valuation kernel -/

universe u
open AlgebraicGeometry
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.Geometry.Building.Kottwitz

/-- The Library's `G(F)^1` is the preimage of the invariant inertia torsion. -/
def CharacterKernelStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    characterValuationKernel (ValuativeRel.valuation F) G =
      (fundamentalInvariantTorsion F (UnramifiedClosure F) (SeparableClosure F) G hG).comap
        (reductiveKottwitzRational F G hG)

end Langlands.Geometry.Building.Kottwitz
