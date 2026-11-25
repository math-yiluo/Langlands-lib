/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomDataSupplement
public import WeilConjectures.CategoryTheory.ClosedScalarHom.ClosedScalarHomComparison

/-! # Canonical scalar internal-Hom isomorphism

Source: Stacks 07A4, 07A6 and 0D6D. The internal-Hom map occurring in the
coherence equations is the explicitly constructed map of the five Hom bijections.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures SheafOfModules
namespace CategoryTheory
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ R : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J R)]
  (M : ScalarHomModels.{c, v, r, w} J) {R S : Sheaf J CommRingCat.{max c v r}}

/-- The explicit comparison furnished by the five representing Hom bijections.
Source: Stacks 07A6 and 08J9 (blueprint: def-sfb-scalar-hom-canonical-iso). -/
noncomputable def scalarHomCanonicalIso (a : R ⟶ S) (μ : ScalarHomTensorComparison M a) :
    scalarHomSource M a ≅ scalarHomTarget.{c, v, r, w} a :=
  ClosedScalarHom.iso (M.closed R) (M.closed S) (M.scalar a).adjunction μ.iso

end CategoryTheory
