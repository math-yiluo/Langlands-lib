import Langlands.GroupScheme.Reductive.SplitUnipotentRadicalMaximal
import Langlands.GroupScheme.Reductive.SplitNormalFppfProductProof
import Langlands.GroupScheme.Reductive.FppfProductUnipotent
import Langlands.GroupScheme.SubgroupFunctor.SmoothConnectedNormalProductExistenceProof
import Langlands.GroupScheme.SubgroupFunctor.FppfProductLaws

/-! # Existence of the split ground-field unipotent radical -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.SplitUnipotentRadicalExistence

open BorelExistence UnipotentRadicalExistence

/-- The split radical exists once represented products of smooth connected normal
closed subgroups exist. -/
theorem splitUnipotentRadicalExistence_of_productExistence
    (hprod : SmoothConnectedNormalFppfProductExistenceStatement.{u}) :
    SplitUnipotentRadicalExistenceStatement.{u} := by
  intro k _ G _ _ _
  have hlft : LocallyOfFiniteType G.X.hom := inferInstance
  obtain ⟨U, i, hi, hmin⟩ := exists_minimal_height_splitCandidate G
  refine ⟨U, i, isSplitUnipotentRadical_of_minimal_height hi hmin ?_⟩
  intro V j hj
  obtain ⟨P, p, hp, hPs, hPc⟩ := hprod k G inferInstance hlft U V i j
    hi.isClosedSubgroup hi.smooth hi.connectedSpace hi.isNormal
    hj.isClosedSubgroup hj.smooth hj.connectedSpace hj.isNormal
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : IsClosedImmersion j.hom.hom.left := hj.isClosedSubgroup
  have : IsAffineHom U.X.hom := by
    rw [← Over.w i.hom.hom]; infer_instance
  have : IsAffineHom V.X.hom := by
    rw [← Over.w j.hom.hom]; infer_instance
  have hU : IsAffine U.X.left := isAffine_of_isAffineHom U.X.hom
  have hV : IsAffine V.X.left := isAffine_of_isAffineHom V.X.hom
  refine ⟨P, p, ⟨⟨hp.isClosedSubgroup, hPs, hPc, ?_, hp.isNormal hi.isNormal hj.isNormal⟩, ?_⟩,
    hp.left_le, hp.right_le⟩
  · exact isUnipotent_fppfProduct i j p hi.isClosedSubgroup hj.isClosedSubgroup hp
      hi.isNormal hU hV hi.isUnipotent hj.isUnipotent
  · exact SplitNormalFppfProduct.splitNormalFppfProduct k G inferInstance hlft U V i j
      hi.isClosedSubgroup hi.smooth hi.connectedSpace hi.isNormal hi.isSplitUnipotent
      hj.isClosedSubgroup hj.smooth hj.connectedSpace hj.isNormal hj.isSplitUnipotent
      P p hp hPs hPc

/-- Every smooth connected affine group scheme over a field has a represented
split ground-field unipotent radical. -/
theorem splitUnipotentRadicalExistence : SplitUnipotentRadicalExistenceStatement.{u} :=
  splitUnipotentRadicalExistence_of_productExistence smoothConnectedNormalFppfProductExistence

end Langlands.GroupScheme.SplitUnipotentRadicalExistence
