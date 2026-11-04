import Langlands.GroupScheme.Reductive.UnipotentRadicalMaximal
import Langlands.GroupScheme.Reductive.FppfProductUnipotent
import Langlands.GroupScheme.SubgroupFunctor.SmoothConnectedNormalProductExistenceProof
import Langlands.GroupScheme.SubgroupFunctor.FppfProductLaws

/-! # Existence of the represented ground-field unipotent radical -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open UnipotentRadicalExistence

/-- Every smooth connected affine group scheme over a field admits its
represented ground-field unipotent radical. -/
theorem unipotentRadicalExistence :
    UnipotentRadicalExistenceStatement.{u} := by
  intro k _ G _ _ _
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨U, i, hi, hmin⟩ := exists_minimal_height_candidate G
  refine ⟨U, i, isUnipotentRadical_of_minimal_height hi hmin ?_⟩
  intro V j hj
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : IsClosedImmersion j.hom.hom.left := hj.isClosedSubgroup
  have hAffU : IsAffine U.X.left := isAffine_of_isAffineHom i.hom.hom.left
  have hAffV : IsAffine V.X.left := isAffine_of_isAffineHom j.hom.hom.left
  obtain ⟨P, p, hprod, hs, hconn⟩ :=
    smoothConnectedNormalFppfProductExistence k G inferInstance inferInstance
    U V i j hi.isClosedSubgroup hi.smooth hi.connectedSpace hi.isNormal
    hj.isClosedSubgroup hj.smooth hj.connectedSpace hj.isNormal
  have huni : IsUnipotent P := isUnipotent_fppfProduct i j p
    hi.isClosedSubgroup hj.isClosedSubgroup hprod hi.isNormal
    hAffU hAffV hi.isUnipotent hj.isUnipotent
  exact ⟨P, p, ⟨hprod.isClosedSubgroup, hs, hconn, huni,
    hprod.isNormal hi.isNormal hj.isNormal⟩, hprod.left_le, hprod.right_le⟩

end Langlands.GroupScheme
