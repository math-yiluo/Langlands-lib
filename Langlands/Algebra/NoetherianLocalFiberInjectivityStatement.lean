import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-! # Noetherian lifting of residue-fibre injectivity -/

universe u v w z

namespace Langlands.Algebra

/-- Stacks Project, Lemma 10.99.1 (tag 00ME), with the residue-fibre map
written as tensor base change and the cokernel as an actual quotient module. -/
def NoetherianLocalFiberInjectivityStatement : Prop :=
  ∀ (R : Type u) (S : Type v) (A : Type w) (B : Type z)
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [IsNoetherianRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module S A] [IsScalarTower R S A]
    [Module.Finite S A] [Module R B] (f : A →ₗ[R] B),
    Module.Flat R B →
    Function.Injective (LinearMap.lTensor (IsLocalRing.ResidueField R) f) →
    Function.Injective f ∧ Module.Flat R (B ⧸ LinearMap.range f)

end Langlands.Algebra
