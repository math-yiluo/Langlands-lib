import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.AffinePoints
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.FieldTheory.IsSepClosed

/-! # Finite étale unipotent groups (Milne 14.14) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Proposition 14.14: let `k` be a field of characteristic exponent `p` and `Ks` a
separable closure of `k`. A finite étale group scheme `G` over `k`, whose order is the number of
its `Ks`-points, is unipotent if and only if its order is a power of `p`. -/
def FiniteEtaleUnipotentOrderStatement : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [ExpChar k p]
    (Ks : Type u) [Field Ks] [Algebra k Ks] [IsSepClosure k Ks]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsFinite G.X.hom] [Etale G.X.hom],
    IsUnipotent G ↔ ∃ n : ℕ, Nat.card (G.affinePoints (CommAlgCat.of k Ks)) = p ^ n

end Langlands.GroupScheme
