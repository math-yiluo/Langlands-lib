import Langlands.AlgebraicGeometry.PointTopology.RationalPoints
import Langlands.GroupScheme.Reductive.Basic
import Langlands.Representation.Smooth.Admissibility.JacquetCartan
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Jacquet–Cartan data on general reductive rational points

The proposition that the rational points `G(F) = RationalPoint F G.X` of every
connected reductive group `G` over a nonarchimedean local field `F`, with the
pinned point topology `rationalPointTopology F G.X`, carry a
`Langlands.JacquetCartanDatum`. This is the structural input of Jacquet's proof
of Renard VI.2.2: standard parabolic pairs, the Iwasawa decomposition, the
Cartan decomposition of standard Levi subgroups, and contraction of their walls.
It is stated here and not assumed or proved.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Aubert.General

universe u

/-- **Jacquet–Cartan data on `G(F)`.** For every nonarchimedean local field `F`
and every connected reductive group `G` over `F`, the rational points `G(F)`,
with their point topology, carry a Jacquet–Cartan datum whose index and wall
types lie in the universe `u` of `F`. -/
def RationalPointsJacquetCartanDatumStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
    Nonempty (JacquetCartanDatum.{u, u} (RationalPoint F G.X))

end Langlands.Aubert.General
