import Langlands.GroupScheme.RelativeLevi.FaceCoverQuotientDescent
import Langlands.GroupScheme.RelativeLevi.FiniteFaceCoverBundle
import Langlands.GroupScheme.RelativeUnipotent.LiftedModuleCharts

/-! # Actual lifted module charts of the original global face quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeLevi.FiniteParabolicFaceCover

open RelativeUnipotent

variable {S : Scheme.{u}} [IsAffine S] {G H U : GroupScheme S}
  [IsAffineHom G.X.hom] {p : H ⟶ G}
  (D : FiniteParabolicFaceCover p)
  (r : U ⟶ H) (hG : IsReductive G) (hp : IsRelativeParabolicSubgroup p)
  (hr : IsRelativeUnipotentRadical r)

/-- The actual globally descended quotient is affine over the original base. -/
lemma globalFaceQuotient_isAffineHom (d : ℕ) :
    IsAffineHom (D.globalFaceQuotientData r hG hp hr d).group.X.hom := by
  let : IsAffine (D.globalFaceQuotientData r hG hp hr d).group.X.left :=
    (D.globalFaceQuotientData r hG hp hr d).affine
  infer_instance

/-- The actual globally descended quotient is smooth, reflected through its
actual original cover comparison. -/
lemma globalFaceQuotient_smooth (d : ℕ) :
    Smooth (D.globalFaceQuotientData r hG hp hr d).group.X.hom := by
  let Q := (D.globalFaceQuotientData r hG hp hr d).group
  let e := (D.globalFaceQuotientData r hG hp hr d).coverIso
  let : Smooth (D.layerGroup d).X.hom := D.smooth_layerGroup d
  let : IsIso e.hom.hom.hom.left :=
    (inferInstance : IsIso (((Grp.forget _) ⋙ Over.forget _).map e.hom))
  have he : Smooth ((baseChange D.groupsBaseMap).obj Q).X.hom := by
    rw [← Over.w e.hom.hom.hom]
    infer_instance
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := Q.X.hom) (g := D.groupsBaseMap)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ he

/-- Original global quotient points, in sections of the actual layer module,
on every test carrying a chosen lift to the original finite affine cover. -/
def globalFaceQuotientCharts (d : ℕ) :
    LiftedModuleCharts D.groupsBaseMap
      (D.globalFaceQuotientData r hG hp hr d).group (D.layerBundle d) :=
  LiftedModuleCharts.ofCoverIso
    (D.globalFaceQuotientData r hG hp hr d).coverIso
    (D.layerBundlePoints d) (D.layerBundlePoints_natural d)

end Langlands.GroupScheme.RelativeLevi.FiniteParabolicFaceCover
