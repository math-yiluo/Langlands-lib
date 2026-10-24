import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-! # The ideal variant of the Noetherian local flatness criterion -/

universe u v w

open scoped TensorProduct

namespace Langlands.Algebra

/-- Stacks Project, Lemma 10.99.10 (tag 00ML), with the Tor-vanishing
hypothesis expressed by injectivity of the ideal's tensor inclusion. -/
def IdealLocalFlatnessCriterionStatement : Prop :=
  ∀ (R : Type u) (S : Type v) (M : Type w)
    [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (I : Ideal R),
    I ≠ ⊤ → Module.Finite S M →
    Function.Injective (LinearMap.rTensor M I.subtype) →
    Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M) →
    Module.Flat R M

end Langlands.Algebra
