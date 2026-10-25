import Mathlib.RingTheory.Flat.Tensor
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-! # The Noetherian local flatness criterion -/

universe u v w

namespace Langlands.Algebra

/-- Stacks Project, Lemma 10.99.7 (tag 00MK), with Tor vanishing
expressed as injectivity of the maximal ideal's tensor inclusion. -/
def LocalFlatnessCriterionStatement : Prop :=
  ∀ (R : Type u) (S : Type v) (M : Type w)
    [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M],
    Function.Injective (LinearMap.rTensor M (IsLocalRing.maximalIdeal R).subtype) →
    Module.Flat R M

end Langlands.Algebra
