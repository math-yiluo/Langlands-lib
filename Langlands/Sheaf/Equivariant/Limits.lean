import Langlands.Sheaf.Equivariant.Topological
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Topology.Sheaves.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Limits of ordinary topological equivariant sheaves

The existing transport-sheaf category inherits actual pointwise limits.
Forgetting transport and evaluating on opens preserve these limits.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe w uX uG uA vA uJ vJ

variable (G : Type uG) [Group G]
variable (X : Type uX) [TopologicalSpace X] [MulAction G X]
variable (A : Type uA) [Category.{vA} A]

section Shape

variable (J : Type uJ) [Category.{vJ} J] [HasLimitsOfShape J A]

instance underlyingPresheaf_preservesLimitsOfShape :
    PreservesLimitsOfShape J (underlyingPresheaf G X A) := by
  exact CategoryTheory.whiskeringLeft_preservesLimitsOfShape J
    (ActionOpens.inclusion G X).op

/-- The ordinary sheaf condition is closed under pointwise transport-presheaf limits. -/
instance sheafProperty_closedUnderLimitsOfShape :
    (sheafProperty G X A).IsClosedUnderLimitsOfShape J := by
  let : PreservesLimitsOfShape J (underlyingPresheaf G X A) :=
    underlyingPresheaf_preservesLimitsOfShape G X A J
  change (ObjectProperty.inverseImage
    (CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology (TopCat.of X)) (A := A))
    (underlyingPresheaf G X A)).IsClosedUnderLimitsOfShape J
  exact ObjectProperty.IsClosedUnderLimitsOfShape.inverseImage J
    (CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology (TopCat.of X)) (A := A))
    (underlyingPresheaf G X A)

/-- Forgetting the sheaf condition creates the specified limits. -/
instance toTransportPresheaf_createsLimitsOfShape :
    CreatesLimitsOfShape J (toTransportPresheaf G X A) := by
  dsimp [toTransportPresheaf]
  infer_instance

/-- These are limits in the actual equivariant sheaf category. -/
instance topologicalSheaf_hasLimitsOfShape :
    HasLimitsOfShape J (TopologicalSheaf G X A) := by
  infer_instance

instance toTransportPresheaf_preservesLimitsOfShape :
    PreservesLimitsOfShape J (toTransportPresheaf G X A) := by
  infer_instance

/-- Forgetting moving-space equivariance and then the sheaf condition is the
same functor as forgetting the sheaf condition and then the transport arrows. -/
def toSheafForgetIso :
    toSheaf G X A ⋙ TopCat.Sheaf.forget A (TopCat.of X) ≅
      toTransportPresheaf G X A ⋙ underlyingPresheaf G X A :=
  Iso.refl _

/-- Forgetting the moving-space equivariance preserves all available limits. -/
instance toSheaf_preservesLimitsOfShape :
    PreservesLimitsOfShape J (toSheaf G X A) := by
  have : PreservesLimitsOfShape J
      (toSheaf G X A ⋙ TopCat.Sheaf.forget A (TopCat.of X)) :=
    preservesLimitsOfShape_of_natIso (toSheafForgetIso G X A).symm
  exact preservesLimitsOfShape_of_reflects_of_preserves (toSheaf G X A)
    (TopCat.Sheaf.forget A (TopCat.of X))

variable {J}

/-- An actual limit, together with all its transport arrows and sheaf gluing. -/
def transportLimit (D : J ⥤ TopologicalSheaf G X A) : TopologicalSheaf G X A :=
  limit D

/-- The canonical limit cone includes equivariant projection maps. -/
def transportLimitCone (D : J ⥤ TopologicalSheaf G X A) : Cone D :=
  limit.cone D

/-- The constructed cone has the full universal property in equivariant sheaves. -/
def transportLimitIsLimit (D : J ⥤ TopologicalSheaf G X A) :
    IsLimit (transportLimitCone G X A D) :=
  limit.isLimit D

/-- Its underlying ordinary sheaf is the actual sheaf limit. -/
def underlyingLimitIso (D : J ⥤ TopologicalSheaf G X A) :
    (toSheaf G X A).obj (transportLimit G X A D) ≅ limit (D ⋙ toSheaf G X A) :=
  preservesLimitIso (toSheaf G X A) D

end Shape

/-- Evaluate an equivariant sheaf on an actual open subset. -/
def evaluation (U : ActionOpens G X) : TopologicalSheaf G X A ⥤ A :=
  toTransportPresheaf G X A ⋙
    (CategoryTheory.evaluation (ActionOpens G X)ᵒᵖ A).obj (op U)

section Shape

variable {J : Type uJ} [Category.{vJ} J] [HasLimitsOfShape J A]

instance evaluation_preservesLimitsOfShape (U : ActionOpens G X) :
    PreservesLimitsOfShape J (evaluation G X A U) := by
  dsimp [evaluation]
  infer_instance

/-- Limits of equivariant sheaves are computed on their actual sections. -/
def limitSectionsIso (D : J ⥤ TopologicalSheaf G X A) (U : ActionOpens G X) :
    (evaluation G X A U).obj (transportLimit G X A D) ≅
      limit (D ⋙ evaluation G X A U) :=
  preservesLimitIso (evaluation G X A U) D

end Shape

section Shapes

/-- Products of every size available in the coefficients. -/
instance topologicalSheaf_hasProducts [HasProducts.{w} A] :
    HasProducts.{w} (TopologicalSheaf G X A) :=
  fun _ => inferInstance

/-- Equalizers available in the coefficients. -/
instance topologicalSheaf_hasEqualizers [HasEqualizers A] :
    HasEqualizers (TopologicalSheaf G X A) :=
  inferInstance

/-- Kernels in the preadditive equivariant sheaf category. -/
instance topologicalSheaf_hasKernels [Preadditive A] [HasEqualizers A] :
    HasKernels (TopologicalSheaf G X A) :=
  inferInstance

/-- Finite limits available in the coefficients. -/
instance topologicalSheaf_hasFiniteLimits [HasFiniteLimits A] :
    HasFiniteLimits (TopologicalSheaf G X A) :=
  ⟨fun _ _ _ => inferInstance⟩

/-- Sections over an open are left exact. -/
instance evaluation_preservesFiniteLimits [HasFiniteLimits A] (U : ActionOpens G X) :
    PreservesFiniteLimits (evaluation G X A U) :=
  ⟨fun _ _ _ => inferInstance⟩

/-- Forgetting moving-space equivariance is left exact. -/
instance toSheaf_preservesFiniteLimits [HasFiniteLimits A] :
    PreservesFiniteLimits (toSheaf G X A) :=
  ⟨fun _ _ _ => inferInstance⟩

end Shapes

end Langlands.Sheaf.Equivariant
