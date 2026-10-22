import Langlands.Geometry.EtalePullback
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Sites.CoverLifting

/-!
# The right adjoint of étale restriction

Right Kan extension exists because base change is right adjoint to composition
on étale objects. Cocontinuity then restricts this right adjoint to sheaves.
-/

noncomputable section

namespace Langlands.Geometry.EtalePullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u vA uA

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]

/-- Base change is right adjoint to composition of étale structure maps. -/
def siteMapPullbackAdjunction :
    siteMap f ⊣ MorphismProperty.Over.pullback (@Etale) ⊤ f :=
  MorphismProperty.Over.mapPullbackAdj (@Etale) ⊤ f (inferInstance : Etale f) trivial

/-- The opposite site map has initial structured-arrow categories. -/
instance rightComma_hasInitial (U : X.Etaleᵒᵖ) :
    HasInitial (StructuredArrow U (siteMap f).op) := by
  let : (siteMap f).op.IsRightAdjoint := (siteMapPullbackAdjunction f).op.isRightAdjoint
  exact isRightAdjoint_iff_hasInitial_structuredArrow.mp inferInstance U

variable (A : Type uA) [Category.{vA} A]

/-- Initial objects compute all limits needed for right Kan extension, even
when the site categories are larger than the coefficient category. -/
instance hasPointwiseRightKanExtension (F : Y.Etaleᵒᵖ ⥤ A) :
    (siteMap f).op.HasPointwiseRightKanExtension F :=
  fun _ => hasLimit_of_domain_hasInitial

/-- The right adjoint of restriction, obtained by right Kan extension. -/
def directImage : Sheaf Y.smallEtaleTopology A ⥤ Sheaf X.smallEtaleTopology A :=
  (siteMap f).sheafPushforwardCocontinuous A Y.smallEtaleTopology X.smallEtaleTopology

/-- Restriction is left adjoint to direct image. -/
def restrictionAdjunction : restriction f A ⊣ directImage f A :=
  (siteMap f).sheafAdjunctionCocontinuous A Y.smallEtaleTopology X.smallEtaleTopology

instance restriction_preservesColimits : PreservesColimits (restriction f A) :=
  (restrictionAdjunction f A).leftAdjoint_preservesColimits

instance directImage_preservesLimits : PreservesLimits (directImage f A) :=
  (restrictionAdjunction f A).rightAdjoint_preservesLimits

end Langlands.Geometry.EtalePullback
