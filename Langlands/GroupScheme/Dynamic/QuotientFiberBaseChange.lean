import Langlands.GroupScheme.Dynamic.BaseChange

/-! # Base change of the right-coset fibre criterion for dynamic parabolic quotients

If two points of a group scheme `G` have the same image under `q : G ⟶ Q` exactly when they differ
by a point of the dynamic parabolic `P_G(χ)`, then the same holds after any base change of the
base scheme, for the base-changed cocharacter.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Base change along any morphism of base schemes preserves the right-coset fibre criterion: if
two points of `G` have the same image under `q` exactly when they differ by a point of the
dynamic parabolic `P_G(χ)`, then the same holds for the base change of `q` and the dynamic
parabolic of the base-changed cocharacter. -/
theorem dynamicParabolicQuotient_fiber_baseChange {S S' : Scheme.{u}} (b : S' ⟶ S)
    {G : GroupScheme S} (χ : (Gm S).toGrp ⟶ G) {Q : Over S} (q : G.X ⟶ Q)
    (hfib : ∀ (T : Over S) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (Dynamic.parabolic χ).carrier T) :
    ∀ (T : Over S') (g h : T ⟶ ((GroupScheme.baseChange b).obj G).X),
      g ≫ (Over.pullback b).map q = h ≫ (Over.pullback b).map q ↔
        g⁻¹ * h ∈ (Dynamic.parabolic (Dynamic.baseChangeCocharacter b χ)).carrier T := by
  intro T g h
  rw [← ((Over.mapPullbackAdj b).homEquiv T Q).symm.injective.eq_iff,
    (Over.mapPullbackAdj b).homEquiv_naturality_right_symm g q,
    (Over.mapPullbackAdj b).homEquiv_naturality_right_symm h q]
  change baseChangePointsEquiv b G T g ≫ q = baseChangePointsEquiv b G T h ≫ q ↔ _
  rw [hfib, Dynamic.parabolic_baseChange, SubgroupFunctor.mem_baseChange, map_mul, map_inv]

end Langlands.GroupScheme
