import Langlands.GroupScheme.SplitSolvableSmoothExtension
import Langlands.GroupScheme.AutomorphicAction.SemidirectMaps
import Langlands.GroupScheme.Rational.SolvableSchemeComparison
import Langlands.GroupScheme.Rational.SplitUnipotentSolvable
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.FieldSeparatedProof

/-! # Split solvability of a split torus acting on a split unipotent group -/

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AutomorphicAction

variable {k : Type u} [Field k]

/-- A commutative group scheme is uniformly solvable: every point group is
commutative, so its first derived subgroup is trivial. -/
theorem isSolvableScheme_of_comm (S : CommGroupScheme (Spec (CommRingCat.of k))) :
    RelativeRoot.IsSolvableScheme S.toGrp := by
  refine ⟨1, fun T => ?_⟩
  let : CommGroup (T ⟶ S.toGrp.X) := Hom.commGroup
  rw [derivedSeries_one]
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr (by
    intro x _
    exact Subgroup.mem_centralizer_iff.mpr fun y _ => mul_comm y x)

variable {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {U : GroupScheme (Spec (CommRingCat.of k))}

/-- The semidirect product of a split torus acting on a smooth connected affine
split unipotent group is split solvable: the normal factor is the kernel of the
projection to the torus, which is an fppf quotient map. -/
theorem isSplitSolvableGroupScheme_semidirectProduct
    (a : AutomorphicAction S.toGrp U) (hS : IsSplitTorus S.toGrp)
    [Smooth U.X.hom] [IsAffineHom U.X.hom] [ConnectedSpace U.X.left]
    (hU : RelativeRoot.IsSplitUnipotent U) :
    IsSplitSolvableGroupScheme a.semidirectProduct := by
  let : Smooth S.toGrp.X.hom := hS.smooth
  let : IsAffineHom S.toGrp.X.hom := hS.isAffineHom
  let : ConnectedSpace S.toGrp.X.left := hS.connectedSpace
  let : IsSeparated S.toGrp.X.hom := fieldSeparated k S.toGrp
  let : GeometricallyConnected U.X.hom := U.geometricallyConnected_of_connected
  let : ConnectedSpace a.semidirectProduct.X.left := by
    change ConnectedSpace ↥(pullback U.X.hom S.toGrp.X.hom)
    infer_instance
  have hq : RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range a.semidirectInl) a.semidirectProjection := by
    have hp : a.semidirectProjection.hom.hom.left =
        pullback.snd U.X.hom S.toGrp.X.hom := by
      rw [semidirectProjection_hom]
      rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hp]
      exact MorphismProperty.pullback_snd (P := @Flat) _ _ inferInstance
    · rw [hp]
      exact MorphismProperty.pullback_snd (P := @Surjective) _ _ inferInstance
    · rw [hp]
      exact MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) _ _
        inferInstance
    · apply SubgroupFunctor.ext
      intro T
      apply Subgroup.ext
      intro x
      rw [mem_range_kernelι_iff, mem_range_semidirectInl_iff]
  exact IsSplitSolvableGroupScheme.of_splitUnipotent_kernel_splitTorus_quotient
    a.semidirectInl a.semidirectProjection a.isClosedSubgroup_semidirectInl hq
    (RelativeRoot.isSolvableScheme_semidirect a (isSolvableScheme_of_comm S)
      hU.isSolvableScheme).isSolvableGroupScheme
    hU hS

end AutomorphicAction

end Langlands.GroupScheme
