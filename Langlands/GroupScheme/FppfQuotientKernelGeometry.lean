import Langlands.GroupScheme.FppfQuotientUniqueness
import Langlands.GroupScheme.Rational.FppfQuotientSmooth
import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.GroupScheme.FppfHomDescent
import Langlands.GroupScheme.RepresentedSubgroup

/-! # Comparison and kernel geometry of arbitrary fppf quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

private theorem schemeMap_isIso {S : Scheme.{u}} {A B : GroupScheme S}
    (e : A ≅ B) : IsIso e.hom.hom.hom.left := by
  have : IsIso e.hom.hom.hom :=
    ⟨⟨e.inv.hom.hom, by rw [← Grp.comp_hom_hom, e.hom_inv_id]; rfl,
      by rw [← Grp.comp_hom_hom, e.inv_hom_id]; rfl⟩⟩
  exact (inferInstance : IsIso ((Over.forget _).map e.hom.hom.hom))

namespace FppfQuotientComparison

variable {S : Scheme.{u}} {G Q R : GroupScheme S} {F : SubgroupFunctor G}
    {q : G ⟶ Q} {r : G ⟶ R}
    (hq : RelativeRoot.IsFppfQuotient F q) (hr : RelativeRoot.IsFppfQuotient F r)

include hq hr in
/-- A supplied fppf quotient is affine whenever another actual quotient
by the same full kernel is affine. -/
theorem isAffineHom_target [IsAffineHom R.X.hom] : IsAffineHom Q.X.hom := by
  have := schemeMap_isIso (fppfIso hq hr)
  rw [← Over.w (fppfIso hq hr).hom.hom.hom]
  infer_instance

end FppfQuotientComparison

namespace RelativeRoot.IsFppfQuotient

variable {S : Scheme.{u}} {G Q Z : GroupScheme S} {F : SubgroupFunctor G}
    {q : G ⟶ Q} {z : Z ⟶ G}
    (hq : RelativeRoot.IsFppfQuotient F q) (hz : F.IsRepresentedBy z)

include hq hz in
/-- A represented full kernel of an fppf homomorphism is flat over the base. -/
theorem flat_representedKernel : Flat Z.X.hom := by
  let : Flat (kernel q).X.hom :=
    MorphismProperty.of_isPullback (kernel_isPullback_scheme q) hq.1
  have := schemeMap_isIso (kernelIso hq hz)
  rw [← Over.w (kernelIso hq hz).hom.hom.hom]
  infer_instance

include hq hz in
/-- A represented full kernel of an fppf homomorphism is locally of finite
presentation over the base. -/
theorem locallyOfFinitePresentation_representedKernel :
    LocallyOfFinitePresentation Z.X.hom := by
  let : LocallyOfFinitePresentation (kernel q).X.hom :=
    MorphismProperty.of_isPullback (kernel_isPullback_scheme q) hq.2.2.1
  have := schemeMap_isIso (kernelIso hq hz)
  rw [← Over.w (kernelIso hq hz).hom.hom.hom]
  infer_instance

end RelativeRoot.IsFppfQuotient

end Langlands.GroupScheme
