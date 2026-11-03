import Langlands.GroupScheme.Absolute.BorelHomogeneousQuotient
import Langlands.GroupScheme.Absolute.CentralizerBorelIntersectionGeometry
import Langlands.GroupScheme.Absolute.CentralizerIntersectionBorelReduction
import Langlands.GroupScheme.Dynamic.ConnectedProof

/-! # The centralizer Borel theorem from closed products and quotient properness -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section ActualIntersection

variable {k : Type u} [Field k]
variable {G M B : GroupScheme (Spec (CommRingCat.of k))}
variable [IsAffineHom G.X.hom]
variable {b : B ⟶ G} (hb : IsBorelSubgroup b)
variable (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
variable (hχ : SubgroupFunctor.range χ ≤ SubgroupFunctor.range b)
variable (j : M ⟶ G) (hj : IsClosedSubgroup j)
variable (hrep : (Dynamic.centralizer χ).IsRepresentedBy j)

/-- Choose the actual homogeneous quotient of the actual intersection with the
prescribed Borel, using its proved smoothness. -/
def IsBorelSubgroup.centralizerIntersectionQuotient (hsm : Smooth M.X.hom) :
    HomogeneousQuotientFromEmbedding.HomogeneousQuotient (subgroupIntersectionFst j b) := by
  have : Smooth M.X.hom := hsm
  have : IsClosedImmersion j.hom.hom.left := hj
  have : IsAffineHom M.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  exact CentralizerProduct.intersectionQuotient j b hb.isClosedSubgroup
    (hb.centralizer_intersection_properties χ hχ j hj hrep).2.1

include hb hχ hj hrep

/-- Closedness of the centralizer--Borel product proves Borel maximality of the
actual first projection under the two explicit proper-quotient inputs. -/
theorem IsBorelSubgroup.centralizer_intersection_isBorel_of_closed_product
    [IsAlgClosed k] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (hproper : ParabolicSubgroupQuotientProperStatement.{u})
    (hcriterion : ProperSolvableQuotientBorelStatement.{u})
    (hsm : Smooth M.X.hom) (hconn : ConnectedSpace M.X.left)
    (hclosed : IsClosed (Set.range (CentralizerProduct.productHom j b).left)) :
    IsBorelSubgroup (subgroupIntersectionFst j b) := by
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
    hb.quotient_isProper_of_parabolicQuotient hproper Q
  have : Smooth Q.projection.left := Q.smooth_projection
  have : Surjective Q.projection.left := Q.surjective_projection
  have : QuasiCompact Q.projection.left := Q.quasiCompact_projection
  have : Smooth R.projection.left := R.smooth_projection
  have : Surjective R.projection.left := R.surjective_projection
  have : QuasiCompact R.projection.left := R.quasiCompact_projection
  have : QuasiCompact R.scheme.hom := R.quasiCompact
  have hRproper : IsProper R.scheme.hom :=
    CentralizerProduct.intersection_quotient_isProper_of_product_closed j b
      Q.projection Q.fibers R.projection R.fibers hclosed
  exact hcriterion k M hconn (subgroupIntersection j b)
    (subgroupIntersectionFst j b) hIclosed hIsm hIconn hIsol R.scheme
    R.projection hRproper R.smooth_projection R.surjective_projection
    R.quasiCompact_projection R.fibers

/-- Taking the actual intersection supplies the required all-test containment. -/
theorem IsBorelSubgroup.exists_centralizer_borel_of_closed_product
    [IsAlgClosed k] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (hproper : ParabolicSubgroupQuotientProperStatement.{u})
    (hcriterion : ProperSolvableQuotientBorelStatement.{u})
    (hsm : Smooth M.X.hom) (hconn : ConnectedSpace M.X.left)
    (hclosed : IsClosed (Set.range (CentralizerProduct.productHom j b).left)) :
    ∃ (C : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ M),
      IsBorelSubgroup c ∧ SubgroupFunctor.range (c ≫ j) ≤ SubgroupFunctor.range b := by
  refine ⟨subgroupIntersection j b, subgroupIntersectionFst j b,
    hb.centralizer_intersection_isBorel_of_closed_product χ hχ j hj hrep
      hproper hcriterion hsm hconn hclosed, ?_⟩
  change SubgroupFunctor.range (subgroupIntersectionHom j b) ≤ SubgroupFunctor.range b
  rw [range_subgroupIntersectionHom]
  exact fun _ _ hx => hx.2

end ActualIntersection

/-- The exact published target reduces to the two named proper-quotient
statements and closedness of the actual products in its original scope. -/
theorem centralizerBorelIntersection_of_closed_products
    (hproper : ParabolicSubgroupQuotientProperStatement.{u})
    (hcriterion : ProperSolvableQuotientBorelStatement.{u})
    (hclosed : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (G : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
      (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
      (M : GroupScheme (Spec (CommRingCat.of k))) (j : M ⟶ G),
      IsClosedSubgroup j → (Dynamic.centralizer χ).IsRepresentedBy j →
      Smooth M.X.hom → ConnectedSpace M.X.left →
      ∀ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G),
        IsBorelSubgroup b → SubgroupFunctor.range χ ≤ SubgroupFunctor.range b →
        IsClosed (Set.range (CentralizerProduct.productHom j b).left)) :
    CentralizerBorelIntersectionStatement.{u} := by
  intro k _ _ G _ _ _ χ M j hj hrep hsm hconn B b hb hχ
  exact hb.exists_centralizer_borel_of_closed_product χ hχ j hj hrep
    hproper hcriterion hsm hconn (hclosed k G χ M j hj hrep hsm hconn B b hb hχ)

end Langlands.GroupScheme
