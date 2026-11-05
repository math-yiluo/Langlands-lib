import Langlands.GroupScheme.SplitExistence.UnipotentLie
import Langlands.GroupScheme.SplitExistence.Opposite

/-! # The Chevalley group for the opposite data

The opposite Chevalley data `D.neg` has the same lattice, weights and root operators as `D`. So a
Chevalley group for `D` is also one for `D.neg`, and its regular cocharacter for `D.neg` is the
one attached to `-ℓ`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.SplitExistence

namespace ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y} {b : P.Base}
  {D : ChevalleyData P b} {k : Type u} [Field k]

/-- A Chevalley group for `D`, viewed as a Chevalley group for `D.neg`. -/
def ChevGroup.neg (G : D.ChevGroup k) : D.neg.ChevGroup k where
  H := G.H
  i := G.i
  smooth := G.smooth
  affine := G.affine
  connected := G.connected
  closed := G.closed
  points := G.points
  t := G.t
  t_comp := G.t_comp
  u := G.u
  u_comp := G.u_comp

@[simp] theorem ChevGroup.neg_H (G : D.ChevGroup k) : G.neg.H = G.H := rfl

@[simp] theorem ChevGroup.neg_i (G : D.ChevGroup k) : G.neg.i = G.i := rfl

@[simp] theorem ChevGroup.neg_t (G : D.ChevGroup k) : G.neg.t = G.t := rfl

theorem neg_eF (j : J) : D.neg.eF (F := k) j = D.eF (F := k) j := rfl

theorem neg_ellWeights : D.neg.ellWeights = -D.ellWeights := rfl

end ChevalleyData

end Langlands.GroupScheme.SplitExistence
