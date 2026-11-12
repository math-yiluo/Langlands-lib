import Langlands.AlgebraicGeometry.AlgebraicSpace.UnipotentOrbitQuotientStatement

/-!
# Rational points of locally separated spaces are locally Hausdorff

Over a henselian valued field `K`, let `X` be a quasi-separated, locally separated
algebraic space locally of finite type. Then every rational point of `X` has an open
neighbourhood in `X(K)` that is Hausdorff, locally compact when `K` is, and totally
disconnected when the norm of `K` is ultrametric. This is the topological claim of
Conrad's Example 5.5, in the corrected form of `UnipotentOrbitQuotientPointTopologyStatement`,
for an arbitrary such space.
-/

noncomputable section

universe u

open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (IsHenselianValuedField)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Rational points of locally separated spaces are locally Hausdorff: for a henselian
valued field `K` and a quasi-separated, locally separated algebraic space `X` locally of
finite type over `Spec K`, every point of `X(K)` has an open neighbourhood that is
Hausdorff, locally compact if `K` is, and totally disconnected if the norm of `K` is
ultrametric. -/
def LocallySeparatedRationalPointsStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K], IsHenselianValuedField K →
    ∀ X : AlgebraicSpace (Spec (CommRingCat.of K)), IsLocallySeparatedLocallyFiniteType K X →
      HasLocallyHausdorffRationalPoints K X

end Langlands.AlgebraicGeometry.AlgebraicSpace
