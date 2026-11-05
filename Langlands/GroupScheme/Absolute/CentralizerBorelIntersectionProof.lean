import Langlands.GroupScheme.Absolute.CentralizerBorelClosedProductReduction
import Langlands.GroupScheme.Absolute.CentralizerBorelProductClosedness
import Langlands.GroupScheme.Absolute.PrescribedBorelQuotient
import Langlands.GroupScheme.Absolute.ProperSolvableQuotient
import Langlands.GroupScheme.SolvableProperFixedPointProof

/-! # A Borel subgroup of a cocharacter centralizer in a prescribed ambient Borel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A Borel containing a cocharacter contains a Borel subgroup of every smooth
connected closed representative of its dynamic centralizer. -/
theorem centralizerBorelIntersection :
    CentralizerBorelIntersectionStatement.{u} := by
  intro k _ _ G _ _ _ χ M j hj hrep hsm hconn B b hb hχ
  have : Smooth M.X.hom := hsm
  have : ConnectedSpace M.X.left := hconn
  have : IsClosedImmersion j.hom.hom.left := hj
  have : IsAffineHom M.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have : IsClosedImmersion b.hom.hom.left := hb.isClosedSubgroup
  have : Mono b.hom.hom := Over.mono_of_mono_left _
  have : Smooth B.X.hom := hb.smooth
  have : IsAffineHom B.X.hom := by
    rw [← Over.w b.hom.hom]
    infer_instance
  obtain ⟨hIclosed, hIsm, _, hIsol, _⟩ :=
    hb.centralizer_intersection_properties χ hχ j hj hrep
  have hr : (Dynamic.centralizer (Dynamic.restrictCocharacter b χ hχ)).IsRepresentedBy
      (subgroupIntersectionSnd j b) :=
    Dynamic.isRepresentedBy_intersectionSnd b hb.isClosedSubgroup
      (Dynamic.restrictCocharacter b χ hχ) j hj (by
        rwa [Dynamic.restrictCocharacter_comp])
  have hIconn : ConnectedSpace (subgroupIntersection j b).X.left :=
    ((dynamicConnected k B (Dynamic.restrictCocharacter b χ hχ)
      (subgroupIntersection j b) (subgroupIntersectionSnd j b)).2 hb.connectedSpace).2 hr
  let Q := hb.homogeneousQuotient
  let R := hb.centralizerIntersectionQuotient χ hχ j hj hrep hsm
  have : IsProper Q.scheme.hom :=
    hb.quotient_isProper_of_solvableProperFixedPoint solvableProperFixedPoint
      Q.scheme Q.projection
      Q.separated Q.locallyOfFiniteType Q.quasiCompact Q.smooth_projection
      Q.surjective_projection Q.quasiCompact_projection Q.fibers
  have : Smooth Q.projection.left := Q.smooth_projection
  have : Surjective Q.projection.left := Q.surjective_projection
  have : QuasiCompact Q.projection.left := Q.quasiCompact_projection
  have : Smooth R.projection.left := R.smooth_projection
  have : Surjective R.projection.left := R.surjective_projection
  have : QuasiCompact R.projection.left := R.quasiCompact_projection
  have : QuasiCompact R.scheme.hom := R.quasiCompact
  have hclosed : IsClosed (Set.range (CentralizerProduct.productHom j b).left) :=
    hb.centralizer_product_isClosed χ hχ j hj hrep hsm hconn
  have hRproper : IsProper R.scheme.hom :=
    CentralizerProduct.intersection_quotient_isProper_of_product_closed j b
      Q.projection Q.fibers R.projection R.fibers hclosed
  have hIborel : IsBorelSubgroup (subgroupIntersectionFst j b) :=
    properSolvableQuotientBorel_of_solvableProperFixedPoint
      solvableProperFixedPoint k M hconn
      (subgroupIntersection j b) (subgroupIntersectionFst j b)
      hIclosed hIsm hIconn hIsol R.scheme R.projection hRproper
      R.smooth_projection R.surjective_projection R.quasiCompact_projection R.fibers
  refine ⟨subgroupIntersection j b, subgroupIntersectionFst j b, hIborel, ?_⟩
  change SubgroupFunctor.range (subgroupIntersectionHom j b) ≤ SubgroupFunctor.range b
  rw [range_subgroupIntersectionHom]
  exact fun _ _ hx => hx.2

end Langlands.GroupScheme
