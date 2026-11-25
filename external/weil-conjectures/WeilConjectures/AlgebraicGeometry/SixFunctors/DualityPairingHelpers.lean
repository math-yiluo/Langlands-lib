/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
@[expose] public section
set_option autoImplicit false
universe c u v w
open CategoryTheory Limits MonoidalCategory
namespace AlgebraicGeometry.Etale

private theorem nativeTensorRaw
    (B : Type c) [Category.{v} B] [Abelian B]
    [IsGrothendieckAbelian.{v} B] [HasDerivedCategory.{w} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [BraidedCategory B]
    [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B] :
    curriedTensor (_root_.DerivedCategory B) =
      @curriedTensor _ _ (DerivedMonoidal.instMonoidalCategory _root_.DerivedCategory.Qh
        (HomotopyCategory.quasiIso B (.up ℤ))) := by
  rfl

/-- The derived étale tensor is definitionally the tensor induced by localization.
This is the concrete specialization needed to instantiate the generic Koszul symmetry. -/
theorem etaleTensorRaw
    (B : Type c) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    (X : Scheme.{u}) : derivedTensor B X =
      @curriedTensor _ _ (DerivedMonoidal.instMonoidalCategory _root_.DerivedCategory.Qh
        (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology B) (.up ℤ))) := by
  exact nativeTensorRaw (Sheaf X.smallEtaleTopology B)

end AlgebraicGeometry.Etale
