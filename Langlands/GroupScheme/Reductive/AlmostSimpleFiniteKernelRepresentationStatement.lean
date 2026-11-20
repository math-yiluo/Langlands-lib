import Langlands.GroupScheme.Reductive.AlmostSimple
import Langlands.GroupScheme.MatrixRepresentation.StableSubrepresentation
import Langlands.AbelianScheme.Kernel
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Almost-simple groups have simple representations with finite kernel (Milne 21.59) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Lemma 21.59: over every field `k`, an almost-simple group `G` has a simple
representation `ρ : G ⟶ GL_n` (`kⁿ ≠ 0` and its only stable subspaces are `0` and `kⁿ`) whose
scheme-theoretic kernel is finite. -/
def AlmostSimpleFiniteKernelRepresentationStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsAlmostSimple G →
      ∃ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)),
        (⊤ : Submodule k (Fin n → k)) ≠ ⊥ ∧
        (∀ W : Submodule k (Fin n → k), ρ.IsStableSubspace W → W = ⊥ ∨ W = ⊤) ∧
        IsFinite (kernel ρ).X.hom

end Langlands.GroupScheme
