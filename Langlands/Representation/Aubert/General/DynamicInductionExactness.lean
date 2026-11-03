import Langlands.Representation.Aubert.General.PrerequisiteStatements
import Langlands.Representation.Aubert.General.DynamicInductionExactnessStatement
import Langlands.GroupScheme.Dynamic.SchemeDecomposition
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup

/-! Exactness of actual dynamic normalized induction for the pinned point topology. -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Aubert.General

section Ring

variable (R : Type u) [CommRing R] [TopologicalSpace R]
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffine G.X.left]
    [IsSeparated G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ G)

/-- Continuity of the actual dynamic limit homomorphism, with the subspace
 topologies induced by the pinned rational-point topology on the original group. -/
theorem continuous_dynamic_limitHom :
    let : TopologicalSpace (RationalPoint R G.X) := rationalPointTopology R G.X
    Continuous (Dynamic.limitHom χ (Over.mk (𝟙 (Spec (CommRingCat.of R))))) := by
  let : TopologicalSpace (RationalPoint R G.X) := rationalPointTopology R G.X
  let P := Dynamic.Affine.parabolicScheme χ
  let Z := Dynamic.Affine.centralizerScheme χ
  let iP := Dynamic.Affine.parabolicHom χ
  let iZ := Dynamic.Affine.centralizerHom χ
  have hP := Dynamic.Affine.isRepresentedBy_parabolicHom χ
  have hZ := Dynamic.Affine.isRepresentedBy_centralizerHom χ
  have hcP := Dynamic.Affine.isClosedSubgroup_parabolicHom χ
  have hcZ := Dynamic.Affine.isClosedSubgroup_centralizerHom χ
  have : IsClosedImmersion iP.hom.hom.left := hcP
  have : IsClosedImmersion iZ.hom.hom.left := hcZ
  have : IsAffine P.X.left := isAffine_of_isAffineHom iP.hom.hom.left
  have : IsAffine Z.X.left := isAffine_of_isAffineHom iZ.hom.hom.left
  let : TopologicalSpace (RationalPoint R P.X) := rationalPointTopology R P.X
  let : TopologicalSpace (RationalPoint R Z.X) := rationalPointTopology R Z.X
  let eP := rationalPointSubgroupHomeomorph R (Dynamic.parabolic χ) iP hP hcP
  let eZ := rationalPointSubgroupHomeomorph R (Dynamic.centralizer χ) iZ hZ hcZ
  have hc := eZ.continuous.comp
    ((continuous_rationalPointMap R (Dynamic.limitGroupHom hP hZ).hom.hom).comp
      eP.symm.continuous)
  have heq : (fun p => eZ (eP.symm p ≫ (Dynamic.limitGroupHom hP hZ).hom.hom)) =
      Dynamic.limitHom χ (Over.mk (𝟙 (Spec (CommRingCat.of R)))) := by
    funext p
    apply Subtype.ext
    change (eP.symm p ≫ (Dynamic.limitGroupHom hP hZ).hom.hom) ≫ iZ.hom.hom =
      Dynamic.limit χ p
    rw [Dynamic.limitGroupHom_comp]
    have hp : hP.pointsEquiv _ (eP.symm p) = p := eP.apply_symm_apply p
    rw [hp]
  exact heq ▸ hc

/-- The semidirect-decomposition projection is the same continuous map. -/
theorem continuous_dynamic_projection :
    let : TopologicalSpace (RationalPoint R G.X) := rationalPointTopology R G.X
    Continuous (dynamic_isSemidirectDecomposition χ
      (Over.mk (𝟙 (Spec (CommRingCat.of R))))).projection := by
  let : TopologicalSpace (RationalPoint R G.X) := rationalPointTopology R G.X
  rw [dynamic_projection_eq_limitHom]
  exact continuous_dynamic_limitHom R G χ

omit [IsSeparated G.X.hom] in
/-- The actual dynamic parabolic is closed in the pinned point topology over
 a Hausdorff topological commutative ring. -/
theorem isClosed_dynamic_parabolic [T2Space R] :
    let : TopologicalSpace (RationalPoint R G.X) := rationalPointTopology R G.X
    IsClosed ((Dynamic.parabolic χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of R)))) :
      Set (RationalPoint R G.X)) := by
  exact isClosed_rationalPoint_subgroup R (Dynamic.parabolic χ)
    (Dynamic.Affine.parabolicHom χ)
    (Dynamic.Affine.isRepresentedBy_parabolicHom χ)
    (Dynamic.Affine.isClosedSubgroup_parabolicHom χ)

end Ring

/-- The actual normalized induction functor preserves short exact sequences of
 finite-length objects, with exactly the published all-local-field binders. -/
theorem dynamicInductionExactness : DynamicInductionExactnessStatement.{u, uV} := by
  intro F _ _ _ _ G hG χ
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
  intro _ _ hU
  let : T2Space F := BruhatTits.localField_t2Space F
  let : T2Space (RationalPoint F G.X) := rationalPoint_t2Space F G
  exact normalizedInductionFunctor_preservesShortExact
    (compactOpenCofinal_of_nonarchimedean _)
    (dynamic_isSemidirectDecomposition χ (Over.mk (𝟙 (Spec (CommRingCat.of F)))))
    hU (isClosed_dynamic_parabolic F G χ) (continuous_dynamic_projection F G χ)

end Langlands.Aubert.General
