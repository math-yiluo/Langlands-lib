import Langlands.GroupScheme.Reductive.AffineReynoldsRegular
import Langlands.GroupScheme.Reductive.InvariantLinearForm
import Langlands.GroupScheme.MatrixRepresentationTensor
import Langlands.GroupScheme.SimplyConnected.Basic

/-! # Embedding torus-invariant regular functions into tensors with an irreducible factor -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme

open AffineLinearEmbedding MatrixRepresentation

/-- For a simply connected semisimple group over an algebraically closed field of
positive characteristic there is an actual diagonalizable subgroup such that every
finite right-stable space of left-invariant regular functions embeds, as an actual
representation, into a tensor product of two representations of equal size whose
first factor is irreducible. This is a proposition to be proved, not an assumed
theorem. -/
def SteinbergTensorEmbeddingStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left],
    IsSimplyConnected G →
    ∃ (Λ : Type u) (_ : AddCommGroup Λ)
      (j : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ G),
      ∀ (V : Submodule k (AffineCoordinates.algebra G)) (d : ℕ) (b : Module.Basis (Fin d) k V)
        (hV : letI := (bialgebra (AffineCoordinates.corepresentation G)).toCoalgebra
          ∀ (f : Module.Dual k (AffineCoordinates.algebra G)) (w : AffineCoordinates.algebra G),
            w ∈ V → rightAct f w ∈ V),
        (∀ w ∈ V, ∀ (T : Over (Spec (CommRingCat.of k)))
          (h : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp.X)
          (g : T ⟶ G.X),
          AffineCoordinates.pointAlgebraHom G T ((h ≫ j.hom.hom) * g) w =
            AffineCoordinates.pointAlgebraHom G T g w) →
        ∃ (m : ℕ) (σ π : MatrixRepresentation G (Fin m))
          (C : Matrix (Fin m × Fin m) (Fin d) k),
          σ.rationalRepresentation.IsIrreducible ∧
            Intertwines (Chevalley.affineRegularRepresentation G V b hV) (σ.tensor π) C ∧
            Function.Injective C.mulVecLin

end Langlands.GroupScheme
