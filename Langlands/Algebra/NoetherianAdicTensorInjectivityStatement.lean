import Langlands.Algebra.NoetherianLocalFiberInjectivityStatement

/-! # Adic passage to ideal-quotient tensor injectivity -/

universe u v w z

namespace Langlands.Algebra

/-- Injectivity modulo all maximal-ideal thickenings of an ideal
descends to injectivity modulo that ideal for a Noetherian finite source. -/
def NoetherianAdicTensorInjectivityStatement : Prop :=
  ∀ (R : Type u) (S : Type v) (A : Type w) (B : Type z)
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [IsNoetherianRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module S A] [IsScalarTower R S A]
    [Module.Finite S A] [Module R B] (f : A →ₗ[R] B) (I : Ideal R),
    (∀ n : ℕ, Function.Injective
      (LinearMap.lTensor (R ⧸ (I ⊔ IsLocalRing.maximalIdeal R ^ n)) f)) →
    Function.Injective (LinearMap.lTensor (R ⧸ I) f)

end Langlands.Algebra
