import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.TorsorCocycle
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.LocalField.Basic

/-! # Local vanishing for simply connected group-scheme cocycles on finite Galois covers -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Every actual cocycle of a semisimple simply connected group over a
nonarchimedean local field, on a finite Galois field cover, is a coboundary.
No restriction on the field characteristic or group isotropy is imposed. -/
def LocalSimplyConnectedGaloisCocycleVanishingStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom],
    IsSimplyConnected G →
    ∀ (M : Type u) [Field M] [Algebra F M] [FiniteDimensional F M] [IsGalois F M]
      (ξ : Cocycle G (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F M))))),
      ξ.IsTrivial

end Langlands.GroupScheme
