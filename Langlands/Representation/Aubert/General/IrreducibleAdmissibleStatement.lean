import Langlands.AlgebraicGeometry.PointTopology.RationalPoints
import Langlands.GroupScheme.Reductive.Basic
import Langlands.Representation.Category.Basic
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Jacquet's theorem for general reductive rational points

The proposition that every irreducible smooth complex representation of the
rational points `G(F) = RationalPoint F G.X` of a connected reductive group `G`
over a nonarchimedean local field `F`, with the pinned point topology
`rationalPointTopology F G.X`, is admissible (Renard VI.2.2). It is stated here
and not assumed or proved.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Aubert.General

universe u uV

/-- **Irreducible implies admissible for `G(F)`** (Jacquet; Renard VI.2.2
Théorème). For every nonarchimedean local field `F` and every connected
reductive group `G` over `F`, every irreducible smooth complex representation of
`G(F)`, with its point topology, is admissible. -/
def RationalPointsIrreducibleAdmissibleStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
    ∀ A : SmoothRep.{0, u, uV} ℂ (RationalPoint F G.X), A.IsIrreducible → A.IsAdmissible

end Langlands.Aubert.General
