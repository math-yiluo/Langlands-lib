import Langlands.Cohomology.DivisibleSystem.DerivedReductionSequence
import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Finite generation of adic étale cohomology

Milne, *Étale Cohomology*, Chapter V, Lemma 1.11, for the Library's actual
étale cohomology of `ℓ`-divisible systems. Under finite cohomology at all
stages, the canonical reduction sequences are short exact and the limit
cohomology is a finite adically complete module.
-/

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Langlands.Geometry

namespace Langlands.Cohomology.DivisibleSystem

universe u wS wR

/-- The adic limit of the torsion-stage étale cohomology of an `ℓ`-divisible
system over an `ℓ`-adically complete coefficient ring is adically complete
and finitely generated if all torsion-stage cohomology groups are finite.
The reduction sequence uses the canonical maps to and from each stage. -/
def EtaleAdicFiniteGenerationStatement
    (X : Scheme.{u}) (R : Type u) [CommRing R] (ℓ : ℕ)
    [IsAdicComplete (Ideal.span {(ℓ : R)}) R]
    [HasDerivedCategory.{wS} (EtaleDerivedSections.ModuleSheaf X R)]
    [HasDerivedCategory.{wR} (ModuleCat.{u} R)] : Prop :=
  ∀ T : DivisibleSystem (EtaleDerivedSections.ModuleSheaf X R) ℓ,
    (∀ m q : ℕ, Finite ((EtaleDerivedSections.cohomology X R q).obj (T.obj m))) →
      (∀ q : ℕ,
        let H := (EtaleAdicCohomology.adicCohomology X R q).obj T.tower
        IsAdicComplete (Ideal.span {(ℓ : R)}) H ∧ Module.Finite R H) ∧
      ∀ r q : ℕ, (etaleReductionSequence X R T r q).ShortExact

end Langlands.Cohomology.DivisibleSystem
