import Langlands.Algebra.LocalApproximationSystem
import Langlands.Algebra.EssFinitePresentation
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Flat.Basic

/-! # Flatness descent along a specified local approximation system -/

universe uI uA uB uN uR uS uM

namespace Langlands.Algebra

/-- Stacks Project, Lemma 10.128.3 (tag 00R6): a specified 00QX approximation
of a flat module has a flat component. All base actions are canonical restrictions. -/
def LocalApproximationFlatnessDescentStatement : Prop :=
  ∀ (ι : Type uI) [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R : Type uR) (S : Type uS) (M : Type uM)
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [AddCommGroup M] [Module S M]
    (D : LocalAlgebraSystem.{uI, uA, uB, uR, uS} ι R S)
    (E : LocalModuleSystem.{uI, uA, uB, uN, uR, uS, uM} D M),
    EssFinitePresentation R S →
    Module.FinitePresentation S M →
    E.IsApproximation →
    letI : Module R M := Module.compHom M (algebraMap R S)
    Module.Flat R M →
      ∃ i : ι,
        letI : Module (D.base i) (E.obj i) :=
          Module.compHom (E.obj i) (algebraMap (D.base i) (D.alg i))
        Module.Flat (D.base i) (E.obj i)

end Langlands.Algebra
