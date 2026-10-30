import Langlands.AlgebraicGeometry.Picard.RigidifiedUniversalBaseChangeStatement
import Langlands.AlgebraicGeometry.Picard.FamilyBaseChangeEquivalence
import Langlands.AlgebraicGeometry.Picard.FamilyBaseChangeNaturality

/-! # Proof: base change of the actual rigidified universal property -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- An actual universal rigidified family remains universal after ground base change. -/
theorem rigidifiedUniversalBaseChange : RigidifiedUniversalBaseChangeStatement.{u} := by
  intro S S' b A P L hL
  rw [RigidifiedLineBundle.isUniversal_iff] at hL ⊢
  intro T M
  let F := familyBaseChange b A T
  let G := familyBaseChangeInverse b A T
  obtain ⟨g, ⟨eg⟩, hg⟩ := hL ((Over.map b).obj T) (G.obj M)
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

end Langlands.AbelianScheme
