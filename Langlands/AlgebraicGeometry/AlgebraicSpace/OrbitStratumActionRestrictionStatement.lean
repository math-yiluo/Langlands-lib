import Langlands.AlgebraicGeometry.AlgebraicSpace.UnipotentOrbitQuotientStatement

/-!
# Smooth group actions restrict to reduced orbit-dimension strata

Over a field `k`, let a smooth group scheme `G` act on a scheme `V` locally of finite
type, and let `i : Z → V` be an immersion of a reduced scheme onto the set of points of
`V` whose orbit has dimension `d`. Then the action restricts to an action on `Z` for
which `i` is equivariant, and every such action has orbit dimension `d` at every point
of `Z`. Conrad's Example 5.5 uses this restricted action on `V_d` without stating it.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open Langlands (GroupScheme)
open Langlands.GroupScheme (SchemeAction)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Smooth group actions restrict to reduced orbit-dimension strata: over a field `k`,
let `G` be a group scheme smooth over `k` acting by `a` on a scheme `V` locally of finite
type over `k`, let `d : ℕ`, and let `i : Z ⟶ V` be an immersion from a reduced scheme
`Z` whose image is the set of points of `V` with orbit dimension `d`. Then there is an
action `b` of `G` on `Z` with `b.hom ≫ i = (G.X ◁ i) ≫ a.hom`, and every action `b` with
this property has orbit dimension `d` at every point of `Z`. -/
def OrbitStratumActionRestrictionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))), Smooth G.X.hom →
    ∀ (V : Over (Spec (CommRingCat.of k))), LocallyOfFiniteType V.hom →
    ∀ (a : SchemeAction G V) (d : ℕ) (Z : Over (Spec (CommRingCat.of k))) (i : Z ⟶ V),
      IsImmersion i.left → IsReduced Z.left →
      Set.range i.left.base = {v : V.left | HasOrbitDimension a v d} →
      (∃ b : SchemeAction G Z, b.hom ≫ i = (G.X ◁ i) ≫ a.hom) ∧
        ∀ b : SchemeAction G Z, b.hom ≫ i = (G.X ◁ i) ≫ a.hom →
          ∀ z : Z.left, HasOrbitDimension b z d

end Langlands.AlgebraicGeometry.AlgebraicSpace
