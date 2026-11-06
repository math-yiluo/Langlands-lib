import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.TorsorCocycle
import Mathlib.FieldTheory.Separable
import Mathlib.NumberTheory.LocalField.Basic

/-! # Local vanishing for simply connected group-scheme cocycles -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Every actual cocycle of a semisimple simply connected group over a
nonarchimedean local field, on a finite separable field cover, is a coboundary.
No restriction on the field characteristic or group isotropy is imposed. -/
def LocalSimplyConnectedCocycleVanishingStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom],
    IsSimplyConnected G →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L]
      [Algebra.IsSeparable F L]
      (ξ : Cocycle G (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F L))))),
      ξ.IsTrivial

end Langlands.GroupScheme
