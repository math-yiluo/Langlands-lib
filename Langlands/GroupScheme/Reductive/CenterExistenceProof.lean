import Langlands.GroupScheme.Reductive.CenterStructureStatement
import Langlands.GroupScheme.FieldFixedSubgroupRepresentabilityProof

/-! # Existence of the full scheme-theoretic centre -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The points fixed by self-conjugation are the full centre, on every test
scheme and after every refinement. -/
theorem conjugation_id_fixedSubgroup_eq_center {S : Scheme.{u}} (G : GroupScheme S) :
    (AutomorphicAction.conjugation (𝟙 G)).fixedSubgroup = center G := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro g
  rw [AutomorphicAction.mem_fixedSubgroup, mem_center]
  constructor
  · intro hg T' b h
    have e := hg T' b h
    simp only [AutomorphicAction.conjugation_act, Grp.id_hom_hom,
      Category.comp_id] at e
    exact (mul_inv_eq_iff_eq_mul.mp e).symm
  · intro hg T' b h
    simp only [AutomorphicAction.conjugation_act, Grp.id_hom_hom,
      Category.comp_id]
    rw [← (hg T' b h).eq, mul_inv_cancel_right]

/-- Every connected reductive group over any field has an actual closed
subgroup representing its full scheme-theoretic centre. -/
theorem schemeTheoreticCenterExistence : SchemeTheoreticCenterExistenceStatement.{u} := by
  intro k _ G hG
  obtain ⟨Z, z, hz, hclosed⟩ :=
    fieldFixedSubgroupRepresentability k G G hG.isAffineHom
      (AutomorphicAction.conjugation (𝟙 G))
  refine ⟨Z, z, hclosed, ?_⟩
  exact hz.2.trans (conjugation_id_fixedSubgroup_eq_center G)

end Langlands.GroupScheme
