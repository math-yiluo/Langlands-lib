import Langlands.GroupScheme.Dynamic.FlagQuotientSchemeAction
import Langlands.GroupScheme.SchemeActionOrbit

/-! # Rational nonfixed quotient sections from movement on a test scheme -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G P H : GroupScheme (Spec (CommRingCat.of k))}
    {Q : Over (Spec (CommRingCat.of k))}

/-- A rational group element moving a quotient section on any test scheme
forces an actual nonfixed rational quotient lift. The source group is smooth;
the quotient target need only be separated. -/
def nonfixedQuotientLiftOfMovingTestPoint
    [Smooth G.X.hom] [IsSeparated Q.hom]
    (i : H ⟶ G) (j : P ⟶ G) (q : G.X ⟶ Q)
    [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    (hfib : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range j).carrier V)
    (t : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)
    (V : Over (Spec (CommRingCat.of k))) (x : V ⟶ G.X)
    (hmove : (((toUnit V ≫ t) ≫ i.hom.hom) * x) ≫ q ≠ x ≫ q) :
    {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X //
      ¬ ((flagQuotientSchemeAction G (SubgroupFunctor.range j) q hfib).restrict i).IsFixed
        (g ≫ q)} := by
  apply Classical.choice
  by_contra hnone
  let a := (flagQuotientSchemeAction G (SubgroupFunctor.range j) q hfib).restrict i
  have hall : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      a.IsFixed (g ≫ q) := by
    intro g
    by_contra hg
    exact hnone ⟨⟨g, hg⟩⟩
  have : IsReduced G.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k G.X.left G.X.hom
  have heq : q ≫ a.translation t = q := by
    apply hom_ext_rationalPoints
    intro g
    rw [← Category.assoc, a.comp_translation]
    have hg := hall g
    have hu : toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k)))) = 𝟙 _ :=
      toUnit_unique _ _
    simpa only [hu, Category.id_comp] using hg _ (𝟙 _) t
  apply hmove
  have h := congrArg (fun z => x ≫ z) heq
  rw [← Category.assoc, a.comp_translation] at h
  change ((flagQuotientSchemeAction G (SubgroupFunctor.range j) q hfib).restrict i).act
      (toUnit V ≫ t) (x ≫ q) = x ≫ q at h
  rwa [SchemeAction.restrict_act, flagQuotientSchemeAction_act_lift] at h

end Langlands.GroupScheme.Dynamic
