/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.ScalarInternalHomData
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.ScalarExtensionBinaryCoherence

/-! # The ordinary normalized scalar tensor comparison

Source: Stacks Project, Modules on Sites, Tags 03EL and 0GMW.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped ChangeOfRings
namespace SheafOfModules.ScalarHomOrdinary
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}}
attribute [local instance] isMonoidal_W_independentCoefficients
attribute [local irreducible] monoidalCategory

/-- The image of a pure section in the sheaf tensor product.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
noncomputable def pure (A : Sheaf J CommRingCat.{r})
    (M N : scalarModules J A) (V : Cᵒᵖ) (x : M.val.obj V) (y : N.val.obj V) :
    ((monoidalCategory A).tensorObj M N).val.obj V :=
  (tensorObjIsoSheafification M N).inv.val.app V
    (((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app
      (M.val ⊗ N.val)).app V (x ⊗ₜ[A.obj.obj V] y))

variable [HasDerivedCategory.{w} (scalarModules J R)]
  [HasDerivedCategory.{w} (scalarModules J S)] (a : R ⟶ S) (s : ScalarDerivedPair a)

end SheafOfModules.ScalarHomOrdinary
