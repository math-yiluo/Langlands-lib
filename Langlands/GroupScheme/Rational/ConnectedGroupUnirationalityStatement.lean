import Langlands.GroupScheme.Reductive.Basic
import Langlands.AlgebraicGeometry.PointTopology.UnirationalDensity
import Mathlib.FieldTheory.Perfect

/-! # Statement: unirationality of connected group varieties -/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

/-- **Unirationality of connected group varieties** (Milne, *Algebraic Groups* (2017),
Theorem 17.93). Let `G` be a smooth connected affine group scheme over a field `k`. Then `G` is
unirational over `k` (there is a dominant morphism over `k` to `G` from a nonempty open
subscheme of a finite-dimensional affine space) in each of the following cases:
1. `k` is perfect;
2. `G` is a connected reductive group. -/
def ConnectedGroupUnirationalityStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    (PerfectField k → Smooth G.X.hom → IsAffineHom G.X.hom → ConnectedSpace G.X.left →
      IsUnirational k G.X) ∧
    (IsConnectedReductive G → IsUnirational k G.X)

end Langlands.GroupScheme
