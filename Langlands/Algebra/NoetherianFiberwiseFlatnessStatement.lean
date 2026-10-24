import Langlands.Algebra.LocalFiberwiseFlatnessStatement
import Mathlib.RingTheory.Noetherian.Basic

/-! # The Noetherian local fibrewise flatness criterion -/

universe u v w z

open scoped TensorProduct

namespace Langlands.Algebra

/-- Stacks Project, Lemma 10.99.15 (tag 00MP). This defines the
Noetherian local fibrewise flatness criterion and does not prove it. -/
def NoetherianFiberwiseFlatnessStatement : Prop :=
  ∀ (R : Type u) (S : Type v) (S' : Type w) (M : Type z)
    [CommRing R] [CommRing S] [CommRing S']
    [IsNoetherianRing R] [IsNoetherianRing S] [IsNoetherianRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S S')]
    [AddCommGroup M] [Module R M] [Module S M] [Module S' M]
    [IsScalarTower R S M] [IsScalarTower S S' M] [IsScalarTower R S' M],
    Module.Finite S' M → Nontrivial M →
    Module.Flat (S ⊗[R] IsLocalRing.ResidueField R)
      ((S ⊗[R] IsLocalRing.ResidueField R) ⊗[S] M) →
    Module.Flat R M →
    Module.Flat R S ∧ Module.Flat S M

end Langlands.Algebra
