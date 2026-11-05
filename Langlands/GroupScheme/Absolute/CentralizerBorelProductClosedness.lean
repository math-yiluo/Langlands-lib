import Langlands.GroupScheme.Absolute.CentralizerProductClosedness
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientReduction
import Langlands.GroupScheme.Absolute.TriangularDiagonalKernelGeometryProof
import Langlands.GroupScheme.UnipotentClosedSubgroupProof
import Langlands.GroupScheme.Rational.TorusUnipotentLiftConjugacy
import Langlands.GroupScheme.Rational.SplitUnipotentStableVectorProof
import Langlands.GroupScheme.Rational.TorusVectorLinearizationProof
import Langlands.GroupScheme.SplitUnipotentAffineTorsorProof
import Langlands.GroupScheme.Unipotent.AlgebraicallyClosedSplit

/-! # Closedness of a centralizer times a Borel containing its cocharacter -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace IsBorelSubgroup

section

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G M B : GroupScheme (Spec (CommRingCat.of k))}
variable [IsAffineHom G.X.hom]
variable {b : B ⟶ G} (hb : IsBorelSubgroup b)
variable (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
variable (hχ : SubgroupFunctor.range χ ≤ SubgroupFunctor.range b)
variable (j : M ⟶ G) (hj : IsClosedSubgroup j)
variable (hrep : (Dynamic.centralizer χ).IsRepresentedBy j)
variable (hsm : Smooth M.X.hom) (hconn : ConnectedSpace M.X.left)

include hb χ hχ j hj hrep hsm hconn

private theorem centralizerProduct_hasRationalClosurePointLifts :
    CentralizerProduct.HasRationalClosurePointLifts j b := by
  let : Smooth M.X.hom := hsm
  let : ConnectedSpace M.X.left := hconn
  let : IsAffineHom M.X.hom :=
    HomogeneousQuotient.affine_subgroup_of_closed G M j hj
  let : IsClosedImmersion b.hom.hom.left := hb.isClosedSubgroup
  let : Mono b.hom.hom := Over.mono_of_mono_left _
  let : Smooth B.X.hom := hb.smooth
  let : ConnectedSpace B.X.left := hb.connectedSpace
  let : IsAffineHom B.X.hom :=
    HomogeneousQuotient.affine_subgroup_of_closed G B b hb.isClosedSubgroup
  obtain ⟨U, D, n, q, hn, hUsm, hUconn, hU, _, hq, hD⟩ :=
    solvableTorusQuotient_of_kernel_prerequisites
      triangularDiagonalKernelGeometry unipotentClosedSubgroup k B hb.isSolvableGroupScheme
  let : Smooth U.X.hom := hUsm
  let : IsAffineHom U.X.hom :=
    HomogeneousQuotient.affine_subgroup_of_closed B U n hn
  have hUsplit := Unipotent.algebraicallyClosedSplit k U hUconn hU
  apply CentralizerProduct.closure_point_factors_of_same_projection
    χ j hrep b hb.isClosedSubgroup hχ q hD
  intro ψ hi
  exact homConjugate_of_isTorus_fppf_split_unipotent_kernel_of_structuralStatements
    RelativeRoot.splitUnipotentStableVectorSubgroup
    RelativeRoot.torusVectorActionLinearization splitUnipotentAffineTorsorStatement
    n hn hUsm hUconn hU hUsplit q hq ψ (Dynamic.restrictCocharacter b χ hχ) hi
    isSplitTorus_gm.isTorus

/-- Choose an actual rational point of the product mapping to a rational point of its
reduced image closure, in the original centralizer--Borel scope. -/
def centralizerProductClosurePointLift
    (a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ CentralizerProduct.imageClosure j b) :
    Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ M.X ⊗ B.X :=
  Classical.choose
    (centralizerProduct_hasRationalClosurePointLifts hb χ hχ j hj hrep hsm hconn a)

/-- The chosen rational product point has the prescribed ambient image. -/
theorem centralizerProductClosurePointLift_comp
    (a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ CentralizerProduct.imageClosure j b) :
    centralizerProductClosurePointLift hb χ hχ j hj hrep hsm hconn a ≫
        CentralizerProduct.productHom j b = a ≫ CentralizerProduct.closureInclusion j b :=
  Classical.choose_spec
    (centralizerProduct_hasRationalClosurePointLifts hb χ hχ j hj hrep hsm hconn a)

variable [Smooth G.X.hom]

/-- In the original centralizer--Borel scope, the actual multiplication image is closed.
No quotient, splitting or conjugacy premise is retained. -/
theorem centralizer_product_isClosed :
    IsClosed (Set.range (CentralizerProduct.productHom j b).left) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Smooth M.X.hom := hsm
  let : IsAffineHom M.X.hom :=
    HomogeneousQuotient.affine_subgroup_of_closed G M j hj
  let : Smooth B.X.hom := hb.smooth
  let : IsAffineHom B.X.hom :=
    HomogeneousQuotient.affine_subgroup_of_closed G B b hb.isClosedSubgroup
  apply CentralizerProduct.product_image_isClosed_of_closure_points j b
  intro a
  exact ⟨centralizerProductClosurePointLift hb χ hχ j hj hrep hsm hconn a,
    centralizerProductClosurePointLift_comp hb χ hχ j hj hrep hsm hconn a⟩

end

end IsBorelSubgroup

end Langlands.GroupScheme
