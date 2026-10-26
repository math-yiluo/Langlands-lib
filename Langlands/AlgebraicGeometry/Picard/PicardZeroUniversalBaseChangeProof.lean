import Langlands.AlgebraicGeometry.Picard.PicardZeroUniversalBaseChangeStatement
import Langlands.AlgebraicGeometry.Picard.PicardZeroFamilyBaseChangeProof
import Langlands.AlgebraicGeometry.Picard.FamilyBaseChangeEquivalence
import Langlands.AlgebraicGeometry.Picard.FamilyBaseChangeNaturality
import Langlands.AlgebraicGeometry.Picard.PicardZeroPullbackProof

/-! # Transport of the actual universal Picard-zero property -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

-- Transport classification using preservation and reflection of the geometric condition.
private theorem universalBaseChange_of_geometric
    (geometric : PicardZeroFamilyBaseChangeStatement.{u}) :
    PicardZeroUniversalBaseChangeStatement.{u} := by
  intro S S' b A P L hL
  obtain ⟨hL, universal⟩ := (isUniversalPicardZero_iff A L).mp hL
  apply (isUniversalPicardZero_iff _ _).mpr
  refine ⟨?_, ?_⟩
  · exact (geometric S S' b A ((Over.pullback b).obj P) _).mp
      (picardZeroPullback S A _ _ (baseChangeParameterMap b P) L hL)
  · intro T M hM
    let F := familyBaseChange b A T
    let G := familyBaseChangeInverse b A T
    let N := G.obj M
    have hN : IsPicardZeroFamily A N :=
      (geometric S S' b A T N).mpr
        ((isPicardZeroFamily_iff_of_iso _
          ((familyBaseChangeCounitIso b A T).app M)).mpr hM)
    obtain ⟨g, ⟨eg⟩, hg⟩ := universal ((Over.map b).obj T) N hN
    let e := baseChangeParameterEquiv b T P
    have mate : baseChangeParameterMate b (e.symm g) = g := e.apply_symm_apply g
    refine ⟨e.symm g, ?_, ?_⟩
    · refine ⟨(baseChangeFamilyPullbackIso b A (e.symm g)).app L ≪≫
        F.mapIso (?_ ≪≫ eg) ≪≫ (familyBaseChangeCounitIso b A T).app M⟩
      exact eqToIso (congrArg (fun k ↦
        (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
          (unitSection_comp A) k).obj L) mate)
    · intro k hk
      apply e.injective
      rw [e.apply_symm_apply]
      apply hg (e k)
      obtain ⟨ek⟩ := hk
      exact ⟨((familyBaseChangeUnitIso b A T).app
        ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
          (unitSection_comp A) (e k)).obj L)).symm ≪≫
        G.mapIso (((baseChangeFamilyPullbackIso b A k).app L).symm ≪≫ ek)⟩

/-- The actual universal Picard-zero family remains universal after ground base change. -/
theorem picardZeroUniversalBaseChange : PicardZeroUniversalBaseChangeStatement.{u} :=
  universalBaseChange_of_geometric picardZeroFamilyBaseChange

end Langlands.AbelianScheme
