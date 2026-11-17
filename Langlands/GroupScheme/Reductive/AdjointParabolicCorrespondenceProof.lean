import Langlands.GroupScheme.Reductive.AdjointParabolicCorrespondenceStatement
import Langlands.GroupScheme.Reductive.AdjointParabolicImage
import Langlands.GroupScheme.Reductive.AdjointParabolicPreimage
import Langlands.GroupScheme.RelativeCentralMultiplicativeTypeQuotient

/-! # Proof: parabolic subgroups of a reductive group and of its adjoint quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The parabolic correspondence between a reductive group and its quotient by
the centre, given the central multiplicative-type quotient construction. -/
theorem adjointParabolicCorrespondence_of
    (hquot : RelativeCentralMultiplicativeTypeQuotientStatement.{u}) :
    AdjointParabolicCorrespondenceStatement.{u} := by
  intro S G hG
  refine ⟨fun P i hi => hi.center_le_range hG, fun Gad q hq => ?_⟩
  have : IsAffineHom Gad.X.hom :=
    AdjointParabolicCorrespondence.isAffineHom_of_isFppfQuotient_center hquot hG hq
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro P i hi
    exact AdjointParabolicCorrespondence.exists_parabolic_image hquot hG hq hi
  · intro P' i' hi'
    exact AdjointParabolicPreimage.exists_relativeParabolic_preimage hG hq hi'
  · intro P₁ P₂ i₁ i₂ hi₁ hi₂ h
    have : Mono i₁.hom.hom := hi₁.mono
    have : Mono i₂.hom.hom := hi₂.mono
    have : Flat q.hom.hom.left := hq.1
    have : Surjective q.hom.hom.left := hq.2.1
    have : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
    exact SubgroupFunctor.range_eq_of_comap_eq_of_fppf q i₁ i₂ h
  · intro P i P' i' hi hi' hrange
    exact AdjointParabolicPreimage.isRelativeBorelSubgroup_iff_of_comap_eq hG hq hi hi' hrange

/-- Parabolic subgroups of a reductive group scheme correspond to those of its
quotient by the centre. -/
theorem adjointParabolicCorrespondence : AdjointParabolicCorrespondenceStatement.{u} :=
  adjointParabolicCorrespondence_of relativeCentralMultiplicativeTypeQuotient

end Langlands.GroupScheme
