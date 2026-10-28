import Langlands.Algebra.EssFinitePresentation
import Langlands.Algebra.LocalAlgebraTowerSystem
import Mathlib.Algebra.Module.FinitePresentation

/-! # Existence of simultaneous local tower approximations -/

universe u v w z

namespace Langlands.Algebra

/-- The supporting existence assertion extracted from the simultaneous construction
in Stacks 00R7, before its flatness argument. All diagrams and the module system
are chosen together in the maximum of the four independent ambient universes.
This definition states the proposition; it does not prove existence. -/
def LocalModuleTowerApproximationExistenceStatement : Prop :=
  ∀ (R : Type u) (S : Type v) (T : Type w) (M : Type z)
    [CommRing R] [CommRing S] [CommRing T]
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S T)]
    [AddCommGroup M] [Module T M],
    EssFinitePresentation R S → EssFinitePresentation R T →
    Module.FinitePresentation T M →
    ∃ (ι : Type (max u v w z)) (_ : Preorder ι) (_ : Nonempty ι)
      (_ : IsDirectedOrder ι)
      (D : LocalAlgebraTowerSystem.{max u v w z, max u v w z,
        max u v w z, max u v w z, u, v, w} ι R S T)
      (E : LocalModuleTowerSystem.{max u v w z, max u v w z,
        max u v w z, max u v w z, max u v w z, u, v, w, z} D M),
      E.IsApproximation

end Langlands.Algebra
