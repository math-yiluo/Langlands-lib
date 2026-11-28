import Langlands.GroupScheme.Rational.ReductiveRadicalCenterStatement
import Langlands.GroupScheme.Rational.AlgClosedNormalSolvableTorusProof
import Langlands.GroupScheme.Rational.CentralSubgroupGeometry
import Langlands.GroupScheme.Reductive.CentralTorusSemisimpleQuotientReduction

/-! # The geometric solvable radical is the reduced connected centre -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The geometric solvable radical is central over the ground field and equals
the reduced identity component of the centre over the algebraic closure. -/
theorem reductiveRadicalCenter :
    ReductiveRadicalCenterStatement.{u} := by
  intro k _ G R r hG hR
  let b := toAlgebraicClosure k
  let B := GroupScheme.baseChange b
  let rbar := B.map r
  have hGbar : IsConnectedReductive (B.obj G) := hG.baseChange_toAlgebraicClosure
  have hr : IsSolvableRadical rbar := hR.2
  obtain ⟨hT, hc⟩ := hR.isTorus_and_isCentral_of_structural
    algClosedReductiveNormalSolvableTorus hG
  refine ⟨hT, hc, ?_⟩
  intro _ Z z hz
  let : Smooth (B.obj G).X.hom := hGbar.smooth
  let : IsAffineHom (B.obj G).X.hom := hGbar.isAffineHom
  let : IsClosedImmersion z.hom.hom.left := hz.1
  let : LocallyOfFiniteType Z.X.hom := by
    rw [← Over.w z.hom.hom]
    infer_instance
  let : IsAffineHom Z.X.hom := by
    rw [← Over.w z.hom.hom]
    infer_instance
  let j := ReducedSubgroup.identityCoreι Z ≫ z
  have hj : IsClosedSubgroup j := by
    change IsClosedImmersion ((ReducedSubgroup.identityCoreι Z).hom.hom.left ≫ z.hom.hom.left)
    infer_instance
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  have hcentral : IsCentral j := hz.isCentral.comp (ReducedSubgroup.identityCoreι Z)
  let C := hcentral.commGroupScheme
  change SubgroupFunctor.range rbar = SubgroupFunctor.range j
  apply le_antisymm
  · let : IsClosedImmersion rbar.hom.hom.left := hr.isClosedSubgroup
    let : Mono rbar.hom.hom := Over.mono_of_mono_left _
    let : Mono z.hom.hom := Over.mono_of_mono_left _
    have hle : SubgroupFunctor.range rbar ≤ SubgroupFunctor.range z := by
      rw [hz.2]
      rintro T _ ⟨x, rfl⟩
      exact hc.baseChange b T x
    obtain ⟨f, hf⟩ := SubgroupFunctor.exists_factor_of_range_le hle
    let : ConnectedSpace (B.obj R).X.left := hr.connectedSpace
    let : Smooth (B.obj R).X.hom := hr.smooth
    let : IsReduced (B.obj R).X.left :=
      Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
        (AlgebraicClosure k) (B.obj R).X.left (B.obj R).X.hom
    let fr := ReducedSubgroup.liftHom f
    apply SubgroupFunctor.range_le_of_factor (IdentityComponent.factor _ fr)
    change IdentityComponent.factor _ fr ≫ (ReducedSubgroup.identityCoreι Z ≫ z) = rbar
    rw [ReducedSubgroup.identityCoreι, Category.assoc, ← Category.assoc
      (IdentityComponent.factor _ fr), IdentityComponent.factor_identityComponentι,
      ← Category.assoc fr, ReducedSubgroup.liftHom_fac, hf]
  · exact hr.greatest _ j hj inferInstance inferInstance
      (isSolvableGroupScheme_of_isCommMonObj C.toGrp) hcentral.range_isNormal

end Langlands.GroupScheme
