import Langlands.GroupScheme.HomScheme.SmoothSplitSourceRepresentabilityProof
import Langlands.AlgebraicGeometry.SmoothPointedEtaleSectionConstruction

/-! # Pointed etale lifting of homomorphisms from a split torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.HomScheme

/-- Every actual homomorphism from a split torus into a smooth affine residue
fibre lifts over a pointed etale neighbourhood, with exact evaluation recovery. -/
def SplitSourcePointedEtaleLiftingStatement : Prop :=
  ∀ (S : Scheme.{u}) (H G : GroupScheme S)
    [Smooth G.X.hom] [IsAffineHom G.X.hom],
    IsSplitTorus H → ∀ (s : S)
      (j₀ : RelativeHom H G (Over.mk (S.fromSpecResidueField s))),
      ∃ (U : Scheme.{u}) (p : U ⟶ S)
        (b : Spec (S.residueField s) ⟶ U)
        (hb : b ≫ p = S.fromSpecResidueField s)
        (j : RelativeHom H G (Over.mk p)),
        Etale p ∧
          evaluate (show Over.mk (S.fromSpecResidueField s) ⟶ Over.mk p from
            Over.homMk b hb) j = j₀

/-- Apply pointed smooth sections to the universal actual Hom scheme. -/
theorem splitSourcePointedEtaleLifting :
    SplitSourcePointedEtaleLiftingStatement.{u} := by
  intro S H G _ _ hH s j₀
  let c := S.fromSpecResidueField s
  obtain ⟨M, i, hi, hM⟩ := smoothSplitSourceRepresentability S H G hH
  obtain ⟨x, hx⟩ := (hi (Over.mk c)).surjective j₀
  let : Smooth M.hom := hM
  obtain ⟨U, p, b, a, hp, hb, ha, hba⟩ :=
    Langlands.AlgebraicGeometry.exists_pointed_etale_section
      M.hom s x.left (Over.w x)
  let aM : Over.mk p ⟶ M := Over.homMk a ha
  let bU : Over.mk c ⟶ Over.mk p := Over.homMk b hb
  have hbaM : bU ≫ aM = x := by
    apply Over.OverMorphism.ext
    exact hba
  refine ⟨U, p, b, hb, evaluate aM i, hp, ?_⟩
  change evaluate bU (evaluate aM i) = j₀
  rw [← evaluate_comp, hbaM]
  exact hx

end Langlands.GroupScheme.HomScheme
