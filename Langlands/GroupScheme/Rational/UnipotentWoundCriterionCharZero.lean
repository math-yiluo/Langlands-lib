import Langlands.GroupScheme.Rational.PointedCommutatorFamily
import Langlands.GroupScheme.Rational.VectorFactorPointedFamilies
import Langlands.GroupScheme.Rational.CommutativeVectorClassificationProof
import Langlands.GroupScheme.Rational.CentralSubgroupGeometry
import Langlands.GroupScheme.Rational.UnipotentWoundCriterionStatement
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Unipotent.PerfectFieldSplitProof
import Langlands.GroupScheme.UnipotentClosedSubgroupProof

/-! # The central additive-subgroup criterion in characteristic zero -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.UnipotentWoundCriterionReduction

variable {k : Type u} [Field k] [CharZero k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

/-- In characteristic zero a nonconstant affine-line map yields an actual
central closed additive line, without a structural theorem premise. -/
theorem exists_central_additive_closed_subgroup_of_charZero
    (hU : IsUnipotent G) (hG : ¬ HasConstantAffineLineMaps G) :
    ∃ (L : GroupScheme (Spec (CommRingCat.of k))) (j : L ⟶ G),
      IsClosedSubgroup j ∧ IsCentral j ∧
        RelativeRoot.IsVectorGroupOfDimension L 1 := by
  obtain ⟨a, n, D, hDs, hDa, _hDgc, hDc, hcent, hnt, _hn, _h₀⟩ :=
    PointedCommutatorFamily.exists_central_generatedImage_of_not_hasConstantAffineLineMaps
      hU hG
  let : IsClosedImmersion D.inclusion.hom.hom.left := D.closed
  let : Mono D.inclusion.hom.hom := D.represents.1
  let : Smooth D.group.X.hom := hDs
  let : IsAffineHom D.group.X.hom := hDa
  let : IsCommMonObj D.group.X := hcent.isCommMonObj
  have hDU : IsUnipotent D.group :=
    unipotentClosedSubgroup k G D.group D.inclusion D.closed hU
  obtain ⟨d, hseries⟩ := perfectFieldUnipotentSplit k D.group hDc hDU
  have hV : RelativeRoot.IsVectorGroupOfDimension D.group d :=
    hseries.isVectorGroupOfDimension_of_commutative
  obtain ⟨L, j, hj, hL⟩ :=
    VectorFactorPointedFamilies.exists_closed_vectorLine hV (hV.pos_of_range_ne_bot hnt)
  exact ⟨L, j ≫ D.inclusion, hj.comp D.closed, hcent.comp j, hL⟩

/-- A chosen actual central closed additive line in characteristic zero. -/
def centralAdditiveLineOfCharZero
    (hU : IsUnipotent G) (hG : ¬ HasConstantAffineLineMaps G) :
    Σ L : GroupScheme (Spec (CommRingCat.of k)),
      {j : L ⟶ G // IsClosedSubgroup j ∧ IsCentral j ∧
        RelativeRoot.IsVectorGroupOfDimension L 1} :=
  Classical.choice (by
    obtain ⟨L, j, hj, hcent, hL⟩ :=
      exists_central_additive_closed_subgroup_of_charZero hU hG
    exact ⟨⟨L, j, hj, hcent, hL⟩⟩)

/-- The central additive-subgroup criterion over every characteristic-zero field. -/
theorem criterion_of_charZero (hU : IsUnipotent G) :
    HasConstantAffineLineMaps G ↔
      ¬ ∃ (L : GroupScheme (Spec (CommRingCat.of k))) (j : L ⟶ G),
        IsClosedSubgroup j ∧ IsCentral j ∧
          RelativeRoot.IsVectorGroupOfDimension L 1 := by
  refine ⟨HasConstantAffineLineMaps.not_exists_central_additive_closed_subgroup, ?_⟩
  intro h
  by_contra hG
  exact h (exists_central_additive_closed_subgroup_of_charZero hU hG)

end Langlands.GroupScheme.UnipotentWoundCriterionReduction
