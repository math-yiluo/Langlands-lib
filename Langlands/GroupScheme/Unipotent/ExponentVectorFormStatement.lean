import Langlands.GroupScheme.VectorGroupQuotient
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-! # Smooth connected commutative groups of exponent `p` are forms of vector groups
(Milne 14.56) -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Milne 2017, Corollary 14.56 with its proof: over a field `k` of characteristic `p > 0`, every
smooth connected commutative affine group scheme `G` killed by `p` becomes isomorphic to a vector
group `𝔾ₐʳ` over a perfect closure `K` of `k` (a perfect field purely inseparable over `k`). -/
def ExponentVectorGroupFormStatement : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (K : Type u) [Field K] [Algebra k K] [PerfectField K] [IsPurelyInseparable k K]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [IsCommMonObj G.X],
    ConnectedSpace G.X.left →
      (∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X), g ^ p = 1) →
        ∃ r : ℕ, Nonempty ((GroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G ≅
            VectorGroup.groupScheme (CommRingCat.of K) r)

end Langlands.GroupScheme
