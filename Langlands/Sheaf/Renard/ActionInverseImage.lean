import Langlands.Sheaf.Renard.StalkActions
import Langlands.Sheaf.Equivariant.DirectImage
import Langlands.Sheaf.Equivariant.Site
import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Inverse image of action sheaves

The existing equivariant inverse-image-on-opens functor is continuous for
the published transport topologies. Left Kan extension and sheafification
therefore give its actual sheaf inverse image.
-/

noncomputable section

namespace Langlands.Sheaf.Renard.SectionActions

open CategoryTheory
open Langlands.Sheaf.Equivariant

variable {G X Y : Type} [Group G]
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [MulAction G X] [MulAction G Y]
variable [ContinuousConstSMul G X] [ContinuousConstSMul G Y]
variable (f : C(X, Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)

/-- The published inverse-image-on-opens functor is continuous for transport sheaves. -/
instance preimage_isContinuous :
    (DirectImage.preimage f hf).IsContinuous
      (transportTopology G Y) (transportTopology G X) where
  op_comp_isSheaf_of_types F := by
    apply (isSheaf_iff_isSheaf_of_type _ _).1
    apply (isSheaf_transportTopology_iff G Y _ _).2
    exact DirectImage.isSheaf f hf _ ⟨F.obj,
      (isSheaf_transportTopology_iff G X _ _).1 F.property⟩

/-- Inverse image on the published equivariant sheaf objects, by Kan extension
and sheafification on the actual transport sites. -/
def actionInverseImage : ActionSheaf G Y ⥤ ActionSheaf G X :=
  (sheafEquivalence G Y (ModuleCat ℂ)).functor ⋙
    Functor.sheafPullbackConstruction.sheafPullback
      (DirectImage.preimage f hf) (ModuleCat ℂ)
      (transportTopology G Y) (transportTopology G X) ⋙
    (sheafEquivalence G X (ModuleCat ℂ)).inverse

/-- The site pullback has its constructed adjunction with precomposition. -/
def actionSiteAdjunction :
    Functor.sheafPullbackConstruction.sheafPullback
        (DirectImage.preimage f hf) (ModuleCat ℂ)
        (transportTopology G Y) (transportTopology G X) ⊣
      (DirectImage.preimage f hf).sheafPushforwardContinuous
        (ModuleCat ℂ) (transportTopology G Y) (transportTopology G X) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (DirectImage.preimage f hf) (ModuleCat ℂ)
    (transportTopology G Y) (transportTopology G X)

/-- On the original action-sheaf categories, inverse image is left adjoint to
the published literal direct image. -/
def actionInverseImageAdjunction :
    actionInverseImage f hf ⊣ DirectImage.sheaf f hf (ModuleCat ℂ) :=
  (((sheafEquivalence G Y (ModuleCat ℂ)).toAdjunction).comp
    (actionSiteAdjunction f hf)).comp
      (sheafEquivalence G X (ModuleCat ℂ)).symm.toAdjunction

section Subgroup

variable [TopologicalSpace G]
variable (Q : Subgroup G)
variable {Z : Type} [TopologicalSpace Z] [MulAction Q Z]
variable [ContinuousConstSMul Q Z]
variable (i : C(Z, Y)) (hi : ∀ (q : Q) (z : Z), i (q • z) = (q : G) • i z)

local instance : ContinuousConstSMul Q Y where
  continuous_const_smul q := continuous_const_smul (q : G)

/-- The underlying restriction sheaf along an equivariant subgroup-space map.
For a locally closed inclusion this is the ordinary algebraic part of Renard's
restriction; smoothness is a separate obligation. -/
def subgroupSpaceRestriction : ActionSheaf G Y ⥤ ActionSheaf Q Z :=
  subgroupRestriction Q ⋙ actionInverseImage i hi

end Subgroup

end Langlands.Sheaf.Renard.SectionActions
