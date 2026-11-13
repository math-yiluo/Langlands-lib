import Langlands.GroupScheme.Rational.HermitianMatrixSplitRankStatement
import Langlands.GroupScheme.Rational.HermitianMatrixSplitRankUpper
import Langlands.GroupScheme.Examples.HermitianHyperbolicSplitRankLower
import Langlands.GroupScheme.Examples.HermitianMatrixPresentationFromPoints

/-! # The attained Hermitian matrix split-rank comparison -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- The actual split rank is the attained maximal totally isotropic dimension. -/
theorem hermitianMatrixSplitRank : HermitianMatrixSplitRankStatement.{u} := by
  intro K L _ _ _ _ _ n _ G _ _ J hJ ρ hρinj hρimage hρnat
  let H : HermitianMatrix.Form (SU3Root.fieldInvolution K L) (Fin (n + 1)) :=
    ⟨J, hJ⟩
  let e := HermitianMatrix.SchemeModel.Presentation.ofMatrixPoints
    K L H G ρ hρinj hρimage hρnat
  have hupper : splitRank G ≤ (H.wittIndex : ℕ∞) :=
    splitRank_le_wittIndex_of_matrixRepresentation H ρ hρinj hρnat
      (fun T x => ((hρimage T (ρ T x)).mp ⟨x, rfl⟩).1)
  have hrank : (H.wittIndex : ℕ∞) = splitRank G :=
    le_antisymm e.wittIndex_le_splitRank hupper
  have hisotropic (W : Submodule L (Fin (n + 1) → L)) :
      H.IsTotallyIsotropic W ↔
        ∀ a b : W, dotProduct (fun i => (SU3Root.fieldInvolution K L).bar (b.val i))
          ((J : Matrix (Fin (n + 1)) (Fin (n + 1)) L).mulVec a.val) = 0 := by
    rw [H.totallyIsotropic_iff_linearFirst]
    constructor
    · intro h a b
      exact (H.linearFirst_eq_dotProduct a.val b.val) ▸ h a.val a.property b.val b.property
    · intro h a ha b hb
      exact (H.linearFirst_eq_dotProduct a b).symm ▸ h ⟨a, ha⟩ ⟨b, hb⟩
  refine ⟨?_, fun W hW => e.finrank_le_splitRank W ((hisotropic W).mpr hW)⟩
  obtain ⟨W, hW, hdim⟩ := H.exists_totallyIsotropic_finrank_eq_wittIndex
  exact ⟨W, (hisotropic W).mp hW, by rw [hdim, hrank]⟩

end Langlands.GroupScheme
