import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.TorsorCocycle
import Langlands.Galois.Local.SeparableInertiaDefinitions
import Mathlib.NumberTheory.LocalField.Basic

/-! # Local vanishing for simply connected cocycles on finite unramified covers -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Every actual cocycle of a semisimple simply connected group over a nonarchimedean local
field `F`, on the cover `Spec E` for a finite unramified extension `E` of `F`, is a coboundary.
Unramified means that `E` lies in the fixed field of the inertia subgroup of
`Gal(SeparableClosure F/F)`. -/
def LocalSimplyConnectedUnramifiedCocycleVanishingStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom],
    IsSimplyConnected G →
    ∀ (E : IntermediateField F (SeparableClosure F)) [FiniteDimensional F E],
      E ≤ LocalGalois.Separable.inertiaFixedField F →
      ∀ ξ : Cocycle G (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F E)))),
        ξ.IsTrivial

end Langlands.GroupScheme
