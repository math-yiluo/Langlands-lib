import Langlands.GroupScheme.MatrixRepresentation.StableSubrepresentation
import Langlands.AbelianScheme.GroupScheme
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Statement: linear reductivity is invariant under extension of the base field -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Linear reductivity under extension of the base field** (Milne, *Algebraic Groups*,
Remark 12.53(c) and its footnote). Let `G` be an affine group scheme of finite type over a
field `k` and let `K` be an extension field of `k`. Then `G` is linearly reductive (every
representation of `G` on `kⁿ` is semisimple: the sum of its simple stable subspaces is
everything) if and only if its base change `G_K` is linearly reductive. No condition is
placed on the extension `K / k`.

This is a statement only; nothing is proved here. -/
def LinearlyReductiveFieldExtensionStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom],
    let IsLinearlyReductive : {F : Type u} → [Field F] →
        GroupScheme (Spec (CommRingCat.of F)) → Prop :=
      fun {F} _ H => ∀ (n : ℕ) (ρ : MatrixRepresentation H (Fin n)),
        sSup {W : Submodule F (Fin n → F) | ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
          ∀ U : Submodule F (Fin n → F), ρ.IsStableSubspace U → U ≤ W →
            U = ⊥ ∨ U = W} = ⊤
    (IsLinearlyReductive G ↔
      IsLinearlyReductive
        ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G))

end Langlands.GroupScheme
