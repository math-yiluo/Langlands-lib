import Langlands.GroupScheme.HomScheme.MultiplicativeTypeSubgroupChartStatements
import Langlands.GroupScheme.Torus.MultiplicativeTypeEtaleLiftReduction

/-! # Pointed étale lifting from a subgroup chart through the prescribed point -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

open TorusSubgroupModuli MultiplicativeTypeSubgroupModuli

/-- A cover by smooth actual multiplicative-type subgroup charts suffices for
pointed étale lifting, without constructing a global representing scheme. -/
theorem multiplicativeTypeEtaleLift_of_chartCover
    (hcover : ChartCoverStatement.{u}) : MultiplicativeTypeEtaleLiftStatement.{u} := by
  intro S G _ _ s H₀ hH₀ i₀ hi₀
  let c := S.fromSpecResidueField s
  obtain ⟨I, M, K, j, hj, hc⟩ := hcover S G
  obtain ⟨k, x, hx⟩ := hc (S.residueField s) c H₀ i₀ hi₀ hH₀
  let : Smooth (M k).hom := (hj k).smooth
  obtain ⟨U, p, b, a, hp, hb, ha, hba⟩ :=
    Langlands.AlgebraicGeometry.exists_pointed_etale_section (M k).hom s x.left (Over.w x)
  let uM : Over.mk p ⟶ M k := Over.homMk a ha
  let bU : Over.mk c ⟶ Over.mk p := Over.homMk b hb
  let H := (baseChange a).obj (K k)
  let i : H ⟶ (baseChange p).obj G := familyHom (j k) uM
  have hi : IsClosedSubgroup i := isClosedSubgroup_familyHom (j k) (hj k).isClosedSubgroup uM
  have hbU : bU ≫ uM = x := by
    apply Over.OverMorphism.ext
    exact hba
  have hieval : evaluate i bU = SubgroupFunctor.range i₀ := by
    change evaluate (familyHom (j k) uM) bU = _
    rw [evaluate_comp, hbU, hx]
  refine ⟨U, p, hp, b, hb, H, (hj k).isMultiplicativeType.baseChange a, i, hi, ?_⟩
  exact @recover_subgroup_fibre_inclusion S G U (Spec (S.residueField s))
    p c b hb H H₀ i i₀ hi hi₀ hieval

end Langlands.GroupScheme
