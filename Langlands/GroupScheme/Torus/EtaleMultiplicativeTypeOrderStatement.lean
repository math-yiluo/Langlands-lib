import Langlands.GroupScheme.Torus.MultiplicativeType
import Langlands.GroupScheme.AffinePoints
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.FieldTheory.IsSepClosed

/-! # Statement: étale groups of multiplicative type (Milne 12.28, last sentence, corrected) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Étale groups of multiplicative type** (Milne, *Algebraic Groups*, Example 12.28, last
sentence, with commutativity added). Let `k` be a field of characteristic exponent `p`, let
`Ks` be a separable closure of `k`, and let `G` be an affine étale group scheme over `k`, whose
order is the number of its `Ks`-points. Then `G` is of multiplicative type if and only if `G` is
commutative and its order is prime to `p`.

Milne's sentence omits commutativity; without it the "if" direction fails, for example for the
constant group `S_3` over `ℚ`.

This is a statement only; nothing is proved here. -/
def EtaleMultiplicativeTypeOrderStatement : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [ExpChar k p]
    (Ks : Type u) [Field Ks] [Algebra k Ks] [IsSepClosure k Ks]
    (G : GroupScheme (Spec (CommRingCat.of k))) [Etale G.X.hom] [IsAffineHom G.X.hom],
    IsMultiplicativeType G ↔
      IsCommMonObj G.X ∧ Nat.Coprime (Nat.card (G.affinePoints (CommAlgCat.of k Ks))) p

end Langlands.GroupScheme
