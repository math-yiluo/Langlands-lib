import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeQuotientStatement
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeCentralizerQuotient
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeCentralizerModel
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeNormalizerQuotientDescent
import Langlands.GroupScheme.Torus.DiagonalizableNormalizerQuotient
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeWeylQuotient

/-! # Assembling multiplicative-type centralizer and normalizer quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

/-- Centralizers and normalizers of closed multiplicative-type subgroups have
smooth relatively quasi-affine homogeneous quotients, and the relative Weyl
quotient is an etale separated quasi-compact group scheme. -/
theorem relativeMultiplicativeTypeQuotient :
    RelativeMultiplicativeTypeQuotientStatement.{u} := by
  have hdiag : DiagonalizableNormalizerQuotientLocalModels.{u} := by
    intro R M _ _ G N _ _ i hi n hn
    exact diagonalizableNormalizer_exists_quasiAffine_quotient_overRing i hi n hn
  intro S G _ _ H i hH hi
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · exact relativeMultiplicativeTypeNormalizer_hasClosedRepresentative i hH hi
  · intro Z z hz
    exact relativeMultiplicativeTypeCentralizer_exists_quasiAffine_quotient i hH hi z hz
  · intro N n hn
    refine ⟨relativeMultiplicativeTypeNormalizer_quotient_of_localModels hdiag i hH hi n hn, ?_⟩
    let : Smooth N.X.hom := relativeMultiplicativeTypeNormalizer_smooth i hH hi n hn
    let : IsClosedImmersion n.hom.hom.left :=
      relativeMultiplicativeTypeNormalizer_isClosedSubgroup i hH hi n hn
    have hnAffine : IsAffineHom (n.hom.hom.left ≫ G.X.hom) := inferInstance
    rw [Over.w n.hom.hom] at hnAffine
    let : IsAffineHom N.X.hom := hnAffine
    obtain ⟨j, hjn, hj, hcent⟩ := multiplicativeTypeSubgroupInNormalizer i hH hi n hn
    let C := relativeMultiplicativeTypeCentralizerModel j hH
    have hc : ((torusCentralizer i).comap n).IsRepresentedBy C.2.val := by
      exact hcent ▸ C.2.property.2.2
    let Q := relativeMultiplicativeTypeCentralizerQuotient j hH hj
      C.2.val C.2.property.2.2
    obtain ⟨W, q, hq⟩ := multiplicativeTypeWeylQuotientOfHomogeneousQuotient
      i hH hi n hn C.2.val hc Q.val
    exact ⟨W, q, hq⟩

end Langlands.GroupScheme
