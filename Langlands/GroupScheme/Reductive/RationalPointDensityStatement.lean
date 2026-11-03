import Langlands.GroupScheme.Reductive.Basic
import Langlands.AlgebraicGeometry.PointTopology.RationalPoints

/-! # Zariski density of rational points of connected reductive groups -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

/-- Over an infinite field, the images of the actual rational points of every
connected reductive group scheme are Zariski dense in its underlying scheme. -/
def ReductiveRationalPointDensityStatement : Prop :=
  ∀ (k : Type u) [Field k] [Infinite k]
    (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    Dense (⋃ p : RationalPoint k G.X, Set.range p.left)

end Langlands.GroupScheme
