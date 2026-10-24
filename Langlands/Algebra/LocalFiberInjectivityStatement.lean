import Langlands.Algebra.EssFinitePresentation
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Lifting injectivity from a local residue fibre -/

universe u v w z

namespace Langlands.Algebra

/-- Stacks Project, Lemma 10.128.4 (tag 046Y), with the residue-fibre map
written as tensor base change and the cokernel as an actual quotient module. -/
def LocalFiberInjectivityStatement : Prop :=
  ∀ (R : Type u) (S : Type v) (M : Type w) (N : Type z)
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module S M] [IsScalarTower R S M]
    [Module R N] [Module S N] [IsScalarTower R S N]
    (f : M →ₗ[S] N),
    EssFinitePresentation R S →
    Module.FinitePresentation S M → Module.FinitePresentation S N →
    Module.Flat R N →
    Function.Injective
      (LinearMap.lTensor (IsLocalRing.ResidueField R) (f.restrictScalars R)) →
    Function.Injective f ∧
      Module.Flat R (N ⧸ LinearMap.range (f.restrictScalars R))

end Langlands.Algebra
