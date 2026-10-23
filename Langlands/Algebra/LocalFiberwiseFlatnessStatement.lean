import Langlands.Algebra.EssFinitePresentation
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # The local fibrewise flatness criterion for essentially finite type algebras -/

universe u v w z

open scoped TensorProduct

namespace Langlands.Algebra

/-- Stacks Project tag 05UV, Lemma 10.128.9. The tensor-product fibre ring is
`S / mS`, and its base change of `M` is `M / mM`, where `m` is the maximal ideal
of `R`. This proposition states the criterion; it does not prove it. -/
def LocalFiberwiseFlatnessStatement : Prop :=
  ∀ (R : Type u) (S : Type v) (S' : Type w) (M : Type z)
    [CommRing R] [CommRing S] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S S')]
    [AddCommGroup M] [Module R M] [Module S M] [Module S' M]
    [IsScalarTower R S M] [IsScalarTower S S' M] [IsScalarTower R S' M],
    EssFinitePresentation R S' → _root_.Algebra.EssFiniteType R S →
    Module.FinitePresentation S' M → Nontrivial M →
    Module.Flat (S ⊗[R] IsLocalRing.ResidueField R)
      ((S ⊗[R] IsLocalRing.ResidueField R) ⊗[S] M) →
    Module.Flat R M →
    EssFinitePresentation R S ∧ Module.Flat R S ∧ Module.Flat S M

end Langlands.Algebra
