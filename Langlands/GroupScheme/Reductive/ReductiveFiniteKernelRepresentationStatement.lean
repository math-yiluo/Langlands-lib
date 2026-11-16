import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.MatrixRepresentation.StableSubrepresentation
import Langlands.AbelianScheme.Kernel
import Mathlib.FieldTheory.Perfect
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Statement: reductive groups over a perfect field are those with a semisimple
representation with finite kernel (Milne 21.60 (a) ⇔ (d)) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Reductivity through a semisimple representation with finite kernel** (Milne,
*Algebraic Groups*, Proposition 21.60, (a) ⇔ (d)). Let `G` be a smooth connected affine group
scheme over a perfect field `k`. Then `G` is reductive if and only if it has a semisimple
representation on some `kⁿ` (the sum of its simple stable subspaces is everything) whose
kernel is finite over `k`.

This is a statement only; nothing is proved here. -/
def ReductiveFiniteKernelRepresentationStatement : Prop :=
  ∀ (k : Type u) [Field k] [PerfectField k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    IsConnectedReductive G ↔
      ∃ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)),
        sSup {W : Submodule k (Fin n → k) | ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
            ∀ U : Submodule k (Fin n → k), ρ.IsStableSubspace U → U ≤ W →
              U = ⊥ ∨ U = W} = ⊤ ∧
          IsFinite (kernel ρ).X.hom

end Langlands.GroupScheme
