import Langlands.AlgebraicGeometry.AlgebraicSpace.UnipotentOrbitQuotientStatement

/-!
# Stabilizers of unipotent actions with constant orbit dimension are smooth

Over a field of characteristic zero, let a unipotent algebraic group `G` act on a reduced
scheme `Z` locally of finite type all of whose points have orbits of the same dimension.
Then the stabilizer scheme is smooth over `Z`. This is the flatness of the action map
over the diagonal asserted in Conrad's Example 5.5, in the stronger smooth form given by
SGA 3, Exposé VI_B, Corollaire 4.4 for group schemes over a reduced base with smooth
fibres of locally constant dimension.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open _root_.AlgebraicGeometry
open Langlands (GroupScheme)
open Langlands.GroupScheme (SchemeAction IsUnipotent)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Stabilizers of unipotent actions with constant orbit dimension are smooth: over a
field `k` of characteristic zero, let `G` be an affine group scheme locally of finite type
over `k` that is unipotent, acting by `b` on a reduced scheme `Z` locally of finite type
over `k`. If every point of `Z` has orbit dimension `d`, then the stabilizer scheme of `b`,
the base change of the action graph `(g, z) ↦ (g.z, z)` along the diagonal of `Z`, is
smooth over `Z`. -/
def UnipotentOrbitStabilizerSmoothStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsAffineHom G.X.hom → LocallyOfFiniteType G.X.hom → IsUnipotent G →
    ∀ (Z : Over (Spec (CommRingCat.of k))), IsReduced Z.left → LocallyOfFiniteType Z.hom →
    ∀ (b : SchemeAction G Z) (d : ℕ), (∀ z : Z.left, HasOrbitDimension b z d) →
      Smooth (pullback.snd (lift b.hom (snd G.X Z)) (lift (𝟙 Z) (𝟙 Z))).left

end Langlands.AlgebraicGeometry.AlgebraicSpace
