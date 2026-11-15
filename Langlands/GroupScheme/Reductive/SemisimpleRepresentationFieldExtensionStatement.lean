import Langlands.GroupScheme.Rational.ValuedRepresentationBaseChange
import Langlands.GroupScheme.MatrixRepresentation.DenseRationalStability
import Langlands.GroupScheme.Lie.RepresentationSubquotient
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Etale.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Simple and semisimple representations under extension of the base field (statement) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Simple and semisimple representations under extension of the base field** (Milne,
*Algebraic Groups* (2017), Proposition 4.19). Let `ρ` be a finite-dimensional representation
of an affine group scheme `G` of finite type over a field `k`, given as a matrix representation
on `k^n`, let `K` be an extension field of `k`, and let `ρK` be the representation of `G_K` on
`K^n` obtained by base change.

* (a) If `ρK` is simple (resp. semisimple), so is `ρ`.
* (b) If `ρ` is simple and its only intertwiners are the scalar matrices, then `ρK` is simple.
* (c) If `ρ` is semisimple and either `K` is separable (algebraic) over `k` or the endomorphism
  algebra of `ρ` is semisimple with étale centre, then `ρK` is semisimple.

Simple is `MatrixRepresentation.IsIrreducible`; as in Milne's Definition 4.15, a representation
is semisimple if it is the sum of its simple subrepresentations (stable subspaces). The
endomorphism algebra is the subalgebra of `Matrix n n k` of matrices intertwining `ρ` with
itself. -/
def SemisimpleRepresentationFieldExtensionStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]
    (n : Type) [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n),
    let ρK := ρ.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    let IsSemisimpleRep : {F : Type u} → [Field F] →
        {H : GroupScheme (Spec (CommRingCat.of F))} → MatrixRepresentation H n → Prop :=
      fun {F} _ {_} σ => sSup {W : Submodule F (n → F) | σ.IsStableSubspace W ∧ W ≠ ⊥ ∧
        ∀ U : Submodule F (n → F), σ.IsStableSubspace U → U ≤ W → U = ⊥ ∨ U = W} = ⊤
    let EndAlg : Subalgebra k (Matrix n n k) :=
      Algebra.adjoin k {C | MatrixRepresentation.Intertwines ρ ρ C}
    ((ρK.IsIrreducible → ρ.IsIrreducible) ∧ (IsSemisimpleRep ρK → IsSemisimpleRep ρ)) ∧
      (ρ.IsIrreducible →
        (∀ C : Matrix n n k, MatrixRepresentation.Intertwines ρ ρ C →
          ∃ c : k, C = Matrix.scalar n c) →
        ρK.IsIrreducible) ∧
      (IsSemisimpleRep ρ →
        (Algebra.IsSeparable k K ∨
          (IsSemisimpleRing EndAlg ∧ Algebra.Etale k (Subalgebra.center k EndAlg))) →
        IsSemisimpleRep ρK)

end Langlands.GroupScheme
