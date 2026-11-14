import Langlands.GroupScheme.Cartan.Basic
import Langlands.AlgebraicGeometry.PointTopology.UnirationalDensity

/-! # Statement: unirational Cartan subgroups give a unirational group -/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

/-- **Unirationality from Cartan subgroups** (Milne, *Algebraic Groups* (2017),
Corollary 17.92). Let `G` be a smooth connected affine group scheme over an infinite field `k`.
If every Cartan subgroup of `G` (the centralizer of a maximal torus of `G`) is unirational
over `k`, then `G` is unirational over `k`. -/
def CartanUnirationalityStatement : Prop :=
  ∀ (k : Type u) [Field k] [Infinite k] (G : GroupScheme (Spec (CommRingCat.of k))),
    Smooth G.X.hom → IsAffineHom G.X.hom → ConnectedSpace G.X.left →
    (∀ (C : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ G),
      IsCartanSubgroup c → IsUnirational k C.X) →
    IsUnirational k G.X

end Langlands.GroupScheme
