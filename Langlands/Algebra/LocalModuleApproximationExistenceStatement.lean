import Langlands.Algebra.EssFinitePresentation
import Langlands.Algebra.LocalApproximationSystem
import Mathlib.Algebra.Module.FinitePresentation

/-! # Existence of local module approximation systems (Stacks 00QX) -/

universe uR uS uM

namespace Langlands.Algebra

/-- Stacks Project, Lemma 10.127.13 (00QX): an essentially finitely presented local
algebra and a finitely presented module admit one joint approximation system.
The three ambient universes are independent; the index and all component
carriers may be chosen in their maximum. This definition states the proposition. -/
def LocalModuleApproximationExistenceStatement : Prop :=
  ∀ (R : Type uR) (S : Type uS) (M : Type uM)
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [AddCommGroup M] [Module S M],
    EssFinitePresentation R S → Module.FinitePresentation S M →
    ∃ (ι : Type (max uR uS uM)) (_ : Preorder ι) (_ : Nonempty ι)
      (_ : IsDirectedOrder ι)
      (D : LocalAlgebraSystem.{max uR uS uM, max uR uS uM, max uR uS uM, uR, uS}
        ι R S)
      (E : LocalModuleSystem.{max uR uS uM, max uR uS uM, max uR uS uM,
        max uR uS uM, uR, uS, uM} D M),
      E.IsApproximation

end Langlands.Algebra
