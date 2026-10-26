import Langlands.Algebra.EssFinitePresentation
import Langlands.Algebra.LocalApproximationMap
import Mathlib.Algebra.Module.FinitePresentation

/-! # Simultaneous local approximation of a module map (Stacks 046Y, first proof step) -/

universe uR uS uM uN

namespace Langlands.Algebra

/-- First paragraph of the proof of Stacks Project, Lemma 10.128.4 (046Y): for an essentially
finitely presented local algebra and an `S`-linear map of finitely presented modules, one ring
system carries approximation systems of both modules (Lemma 10.127.13, 00QX) and compatible
component maps inducing the given map. The four ambient universes are independent; the index
and all component carriers may be chosen in their maximum. This definition states the
proposition. -/
def LocalCompatibleMapApproximationExistenceStatement : Prop :=
  ∀ (R : Type uR) (S : Type uS) (M : Type uM) (N : Type uN)
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N],
    EssFinitePresentation R S → Module.FinitePresentation S M →
    Module.FinitePresentation S N → ∀ f : M →ₗ[S] N,
    ∃ (ι : Type (max uR uS uM uN)) (_ : Preorder ι) (_ : Nonempty ι)
      (_ : IsDirectedOrder ι)
      (D : LocalAlgebraSystem.{max uR uS uM uN, max uR uS uM uN, max uR uS uM uN, uR, uS}
        ι R S)
      (E : LocalModuleSystem.{max uR uS uM uN, max uR uS uM uN, max uR uS uM uN,
        max uR uS uM uN, uR, uS, uM} D M)
      (F : LocalModuleSystem.{max uR uS uM uN, max uR uS uM uN, max uR uS uM uN,
        max uR uS uM uN, uR, uS, uN} D N)
      (φ : LocalModuleSystem.CompatibleMap E F f),
      φ.IsApproximation

end Langlands.Algebra
