import Langlands.AlgebraicGeometry.Modules.FormalModuleSystem
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Noetherian.Defs

/-! # Proper coherent formal existence over complete local rings: statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

/-- A compatible system of locally finitely presented actual module sheaves on
maximal-ideal thickenings of a proper scheme over a complete local noetherian
ring has a locally finitely presented algebraization, with one comparison
commuting with all transition maps. -/
def ProperFormalCoherentExistenceStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)), IsProper f →
      ∀ F : FormalModuleSystem f (IsLocalRing.maximalIdeal R),
        (∀ n, (F.obj n).IsFinitePresentation) →
          ∃ M : X.Modules, M.IsFinitePresentation ∧
            FormalModuleSystem.IsAlgebraization M F

end Langlands.AlgebraicGeometry.Modules
