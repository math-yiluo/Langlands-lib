import Langlands.GroupScheme.Torus.LatticeGalois
import Langlands.GroupScheme.Torus.KernelDiagonalizable
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Finiteness

/-! # Finite Galois full faithfulness for groups of multiplicative type: statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Finite Galois full faithfulness for groups of multiplicative type**, derived from
Milne, *Algebraic Groups* (2017), Theorem 12.23. Suppose that two commutative group schemes
over `k` become diagonalizable over a common finite Galois extension `L/k`, with finitely
generated abelian character groups that may have torsion. An additive map between their
actual `L`-character groups is Galois equivariant if and only if it is the pullback of
characters along exactly one ground-field homomorphism. -/
def MultiplicativeTypeGaloisFullFaithfulnessStatement : Prop :=
  ∀ (k L : Type u) [Field k] [Field L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (T T' : CommGroupScheme (Spec (CommRingCat.of k)))
    (M M' : Type u) [AddCommGroup M] [AddCommGroup M'] [AddGroup.FG M] [AddGroup.FG M']
    (_i : (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T ≅
      Diagonalizable.groupScheme (CommRingCat.of L) M)
    (_i' : (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T' ≅
      Diagonalizable.groupScheme (CommRingCat.of L) M')
    (F : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T') →+
      characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)),
    (∀ (σ : L ≃ₐ[k] L)
      (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T')),
      F (characterLattice.galoisRepresentation k L T' σ χ) =
        characterLattice.galoisRepresentation k L T σ (F χ)) ↔
    ∃! a : T ⟶ T',
      ∀ χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T'),
        (CommGroupScheme.baseChange (algebraBaseMap k L)).map a ≫ χ = F χ

end Langlands.GroupScheme
