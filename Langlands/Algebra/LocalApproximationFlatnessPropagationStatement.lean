import Langlands.Algebra.LocalApproximationSystem
import Mathlib.RingTheory.Flat.Basic

/-! # Forward propagation of component flatness in local approximation systems -/

universe uI uA uB uN uR uS uM

namespace Langlands.Algebra

/-- Component flatness propagates along a canonical prime-localization transition
whose canonical module base-change map is bijective. Both base actions are
restrictions of the given component algebra actions. This is a statement only. -/
def LocalApproximationFlatnessPropagationStatement : Prop :=
  ∀ (ι : Type uI) [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R : Type uR) (S : Type uS)
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    (M : Type uM) [AddCommGroup M] [Module S M]
    (D : LocalAlgebraSystem.{uI, uA, uB, uR, uS} ι R S)
    (E : LocalModuleSystem.{uI, uA, uB, uN, uR, uS, uM} D M)
    (i j : ι) (h : i ≤ j),
    D.IsPrimeLocalization h →
    Function.Bijective (E.moduleBaseChangeMap h) →
    letI : Module (D.base i) (E.obj i) :=
      Module.compHom (E.obj i) (algebraMap (D.base i) (D.alg i))
    letI : Module (D.base j) (E.obj j) :=
      Module.compHom (E.obj j) (algebraMap (D.base j) (D.alg j))
    Module.Flat (D.base i) (E.obj i) →
    Module.Flat (D.base j) (E.obj j)

end Langlands.Algebra
