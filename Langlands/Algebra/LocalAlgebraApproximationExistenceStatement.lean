import Langlands.Algebra.EssFinitePresentation
import Langlands.Algebra.LocalApproximationSystem

/-! # Existence of local algebra approximation systems (Stacks 00QV) -/

universe uR uS

namespace Langlands.Algebra

/-- Stacks 00QV: every essentially finitely presented local algebra map admits
a directed local algebra approximation system. The index and component rings
are chosen in the maximum of the independent ambient universes. -/
def LocalAlgebraApproximationExistenceStatement : Prop :=
  ∀ (R : Type uR) (S : Type uS)
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)],
    EssFinitePresentation R S →
    ∃ (ι : Type (max uR uS)) (_ : Preorder ι) (_ : Nonempty ι)
      (_ : IsDirectedOrder ι)
      (D : LocalAlgebraSystem.{max uR uS, max uR uS, max uR uS, uR, uS} ι R S),
      D.IsApproximation

end Langlands.Algebra
