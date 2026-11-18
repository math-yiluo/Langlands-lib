import Langlands.GroupScheme.Reductive.InnerFormStarActionStatement
import Langlands.GroupScheme.Reductive.InnerFormStarForward
import Langlands.GroupScheme.Reductive.CommonFiniteStageStarEquivalence
import Langlands.GroupScheme.Reductive.PinnedIsomorphismProof
import Langlands.GroupScheme.Reductive.StarCompatibleInnerTwist

/-! # Inner forms are detected by the star action -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- Inner forms over a field are exactly the forms with equivalent absolute star actions. -/
theorem innerFormStarAction : InnerFormStarActionStatement.{u} := by
  intro k _ G H A _ _ _ _ q hq d d'
  constructor
  · rintro ⟨L, _, _, _, _, E, hE⟩
    exact InnerFormStarForward.of_localIso hq d d' E hE
  · rintro ⟨f, hb, hstar⟩
    obtain ⟨L, _, _, _, _, δ, δ', fL, hbL, hstarL⟩ :=
      commonFiniteStageStarEquivalence k G H d d' f hb hstar
    obtain ⟨E, hE, _⟩ :=
      pinnedIsomorphism L _ _ δ.toSplitPinning δ'.toSplitPinning fL hbL
    let C := StarCompatibleInnerTwist.Comparison.ofPinnedIso δ δ' E
    have he (χ : characterLattice δ.toSplitPinning.torus) :
        fL.weightMap χ = C.torusIso.inv ≫ χ := by
      have h := congrArg
        (fun z : characterLattice δ.toSplitPinning.torus ≃ₗ[ℤ]
          characterLattice δ'.toSplitPinning.torus => z χ) hE.1
      exact h.symm
    refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
      LocalGroupIso.ofBaseChangeIso E.groupIso, ?_⟩
    exact StarCompatibleInnerTwist.hasInnerDiscrepancy δ δ' C fL he hbL hstarL hq

end Langlands.GroupScheme
