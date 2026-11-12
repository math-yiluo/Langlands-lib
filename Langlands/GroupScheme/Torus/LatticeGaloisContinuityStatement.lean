import Langlands.GroupScheme.Torus.LatticeGalois
import Langlands.GroupScheme.Torus.Split
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! # Continuity of the Galois action on the lattices of a torus: statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Let `E/k` be an algebraic extension and `T` a commutative group scheme over `k` whose base
change to `E` is a split torus. Then a finite-dimensional intermediate field `L` exists such
that every `σ ∈ Aut_k(E)` fixing `L` pointwise acts trivially on `X^*(T_E)` and on
`X_*(T_E)`. -/
def TorusLatticeGaloisContinuityStatement : Prop :=
  ∀ (k E : Type u) [Field k] [Field E] [Algebra k E] [Algebra.IsAlgebraic k E]
    (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T).toGrp →
      ∃ L : IntermediateField k E, FiniteDimensional k L ∧
        ∀ σ : E ≃ₐ[k] E, (∀ x ∈ L, σ x = x) →
          characterLattice.galoisRepresentation k E T σ = 1 ∧
            cocharacterLattice.galoisRepresentation k E T σ = 1

end Langlands.GroupScheme
