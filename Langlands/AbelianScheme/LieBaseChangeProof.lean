import Langlands.AbelianScheme.LieBaseChangeStatement
import Langlands.AlgebraicGeometry.PullbackFiniteLocalBasisRankProof
import Langlands.AlgebraicGeometry.ModuleDualPullbackLocalFree
import Langlands.AlgebraicGeometry.SmoothDifferentialsFiniteLocalBasisRank
import Langlands.AbelianScheme.CotangentBaseChangeProof

/-! # Proof of canonical Lie base change for abelian schemes -/

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

namespace Langlands.AbelianScheme

/-- Lie base change follows from cotangent base change and finite local bases of smooth
differentials. -/
theorem lieBaseChange_of (S : AlgebraicGeometry.Scheme.{u})
    (hc : GroupScheme.CotangentBaseChangeIsIsoStatement S)
    (hd : Langlands.Scheme.SmoothDifferentialsFiniteLocalBasisRankStatement.{u}) :
    LieBaseChangeStatement S := by
  intro T b A
  have hiso : IsIso (GroupScheme.cotangentBaseChangeMap b A.toGrp) := hc T b A.toGrp
  refine ⟨hiso, ?_⟩
  obtain ⟨q, hq₁, hq₂⟩ := (hd _ _ A.X.hom).1 A.smooth
  obtain ⟨q', hq₁', hq₂'⟩ := (Langlands.Scheme.Modules.pullbackFiniteLocalBasisRank _ _
    (GroupScheme.identitySection A.toGrp) _).1 ⟨q, hq₁, hq₂⟩
  have hdp : IsIso (Langlands.Scheme.Modules.dualPullbackComparison b
      (GroupScheme.cotangentAtIdentity A.toGrp)) :=
    @Langlands.Scheme.Modules.isIso_dualPullbackComparison_of_localGeneratorsData _ _ b _ q'
      hq₁' hq₂'
  refine ⟨@asIso _ _ _ _ (Langlands.Scheme.Modules.dualPullbackComparison b
      (GroupScheme.cotangentAtIdentity A.toGrp)) hdp ≪≫
    (asIso (Langlands.Scheme.Modules.dualMap
      (GroupScheme.cotangentBaseChangeMap b A.toGrp))).symm, ?_⟩
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => Langlands.Scheme.Modules.dualPullbackComparison b
      (GroupScheme.cotangentAtIdentity A.toGrp) ≫ k) (IsIso.inv_hom_id
        (Langlands.Scheme.Modules.dualMap (GroupScheme.cotangentBaseChangeMap b A.toGrp)))).trans
      (Category.comp_id _))

/-- Lie base change follows from cotangent base change, using the published finite local bases
of smooth differentials. -/
theorem lieBaseChange_of_cotangent (S : AlgebraicGeometry.Scheme.{u})
    (hc : GroupScheme.CotangentBaseChangeIsIsoStatement S) :
    LieBaseChangeStatement S :=
  lieBaseChange_of S hc Langlands.Scheme.smoothDifferentialsFiniteLocalBasisRank

/-- Canonical Lie base change for abelian schemes over an arbitrary base. -/
theorem lieBaseChange (S : AlgebraicGeometry.Scheme.{u}) : LieBaseChangeStatement S :=
  lieBaseChange_of_cotangent S (GroupScheme.cotangentBaseChangeIsIso S)

end Langlands.AbelianScheme
