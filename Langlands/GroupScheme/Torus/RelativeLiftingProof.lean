import Langlands.GroupScheme.Torus.RelativeLiftingStatement
import Langlands.GroupScheme.HomScheme.SmoothSplitSourceRepresentabilityProof
import Langlands.GroupScheme.HomScheme.FibreComparison
import Langlands.GroupScheme.Torus.ClosedImmersionLocus
import Langlands.AlgebraicGeometry.SmoothPointedEtaleSectionConstruction

/-! # Pointed etale lifting of an actual closed split torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

open HomScheme

/-- A closed split torus in a residue fibre of a smooth affine group scheme lifts
to a split torus over a pointed etale neighbourhood, with the exact original inclusion. -/
theorem relativeSplitTorusLifting : RelativeSplitTorusLiftingStatement.{u} := by
  intro S G _ _ s T₀ hT₀ i₀ hi₀
  obtain ⟨I, hI, ⟨eI⟩⟩ := hT₀
  let c := S.fromSpecResidueField s
  let H := splitTorus S I
  let e₀ : (baseChange c).obj H ≅ T₀ :=
    splitTorus.baseChangeIso c I ≪≫ eI.symm
  let j₀ : RelativeHom H G (Over.mk c) := e₀.hom ≫ i₀
  have hj₀ : IsClosedImmersion j₀.hom.hom.left := by
    change IsClosedImmersion (e₀.hom.hom.hom.left ≫ i₀.hom.hom.left)
    infer_instance
  obtain ⟨M, i, hi, hM⟩ :=
    smoothSplitSourceRepresentability S H G (isSplitTorus_splitTorus I)
  obtain ⟨x, hx⟩ := (hi (Over.mk c)).surjective j₀
  change evaluate x i = j₀ at hx
  have hxclosed : IsClosedImmersion ((baseChange x.left).map i).hom.hom.left := by
    apply (isClosedImmersion_evaluate_iff x i).mp
    rw [hx]
    exact hj₀
  have : IsAffineHom ((baseChange M.hom).obj G).X.hom := by
    change IsAffineHom (Limits.pullback.snd G.X.hom M.hom)
    exact MorphismProperty.pullback_snd _ _ ‹IsAffineHom G.X.hom›
  obtain ⟨V, q, hq, bx, hbx, hqclosed⟩ :=
    exists_open_isClosedImmersion_baseChange ((isSplitTorus_splitTorus I).baseChange M.hom)
      i (S.residueField s) x.left hxclosed
  let v : Over S := Over.mk (q ≫ M.hom)
  let vM : v ⟶ M := Over.homMk q rfl
  have hvclosed : IsClosedImmersion (evaluate vM i).hom.hom.left :=
    (isClosedImmersion_evaluate_iff vM i).mpr hqclosed
  let hvSmooth : Smooth v.hom := by
    dsimp [v]
    infer_instance
  have hbxc : bx ≫ v.hom = c := by
    dsimp [v]
    rw [← Category.assoc, hbx]
    exact Over.w x
  obtain ⟨U, p, b, a, hp, hb, ha, hba⟩ :=
    Langlands.AlgebraicGeometry.exists_pointed_etale_section v.hom s bx hbxc
  let uV : Over.mk p ⟶ v := Over.homMk a ha
  let uM : Over.mk p ⟶ M := uV ≫ vM
  let j : RelativeHom H G (Over.mk p) := evaluate uM i
  have hjclosed : IsClosedImmersion j.hom.hom.left := by
    dsimp [j, uM]
    rw [evaluate_comp]
    exact isClosedImmersion_evaluate uV (evaluate vM i) hvclosed
  let bU : Over.mk c ⟶ Over.mk p := Over.homMk b hb
  have hbU : bU ≫ uM = x := by
    apply Over.OverMorphism.ext
    change b ≫ a ≫ q = x.left
    rw [← Category.assoc, hba, hbx]
  have hjeval : evaluate bU j = e₀.hom ≫ i₀ := by
    change evaluate bU (evaluate uM i) = j₀
    rw [← evaluate_comp, hbU, hx]
  refine ⟨U, p, hp, b, hb, (baseChange p).obj H,
    (isSplitTorus_splitTorus I).baseChange p, j, hjclosed, ?_⟩
  exact recover_fibre_inclusion p c b hb T₀ e₀ j i₀ hjeval

end Langlands.GroupScheme
