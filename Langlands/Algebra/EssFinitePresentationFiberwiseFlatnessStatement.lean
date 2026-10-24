import Langlands.Algebra.LocalFiberwiseFlatnessStatement

/-! # Fibrewise flatness for essentially finitely presented local algebras -/

universe u v w z

open scoped TensorProduct

namespace Langlands.Algebra

/-- Stacks Project, Lemma 10.128.8 (tag 00R7). Both local algebras are essentially
finitely presented. This definition states the criterion and does not prove it. -/
def EssFinitePresentationFiberwiseFlatnessStatement : Prop :=
  ∀ (R : Type u) (S : Type v) (S' : Type w) (M : Type z)
    [CommRing R] [CommRing S] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S S')]
    [AddCommGroup M] [Module R M] [Module S M] [Module S' M]
    [IsScalarTower R S M] [IsScalarTower S S' M] [IsScalarTower R S' M],
    EssFinitePresentation R S → EssFinitePresentation R S' →
    Module.FinitePresentation S' M → Nontrivial M →
    Module.Flat (S ⊗[R] IsLocalRing.ResidueField R)
      ((S ⊗[R] IsLocalRing.ResidueField R) ⊗[S] M) →
    Module.Flat R M →
    Module.Flat R S ∧ Module.Flat S M

end Langlands.Algebra
