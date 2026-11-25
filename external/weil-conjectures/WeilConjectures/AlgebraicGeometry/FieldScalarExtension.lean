/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FieldScalarPresheafPullbackExists
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-! # Scalar extension of module-valued sheaves

Source: Stacks Project, Sheaves on Spaces, Tags 0095 and 0096.
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace SheafOfModules

/-- Abelian-group sheafification exists in any universe containing the small site. -/
theorem fieldScalarExtension_hasSheafify (X : TopCat.{u}) :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v} := by
  let : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget AddCommGrpCat.{max u v}) :=
    preservesFilteredColimitsOfSize_shrink _
  infer_instance

/-- Local bijectivity detects sheafification equivalences in the enlarged universe. -/
theorem fieldScalarExtension_wEqualsLocallyBijective (X : TopCat.{u}) :
    (Opens.grothendieckTopology X).WEqualsLocallyBijective
      AddCommGrpCat.{max u v} := by
  let : EssentiallySmall.{max u v} (Opens X) := essentiallySmallSelf.{v} (Opens X)
  let : PreservesFilteredColimitsOfSize.{max u v, max u v}
      (CategoryTheory.forget AddCommGrpCat.{max u v}) := preservesFilteredColimitsOfSize_shrink _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    (Opens.grothendieckTopology X) (A := AddCommGrpCat.{max u v})

variable {k : Type u} [Ring k] (X : TopCat.{u})
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  (α : k →+* R.obj.obj (op ⊤))

/-- Scalar extension: forget the sheaf condition, pull back modules over the constant
ring presheaf, and sheafify. The pullback is specified by its adjunction.
(blueprint: def-sc-field-scalar-extension). -/
noncomputable def fieldScalarExtension :
    Sheaf (Opens.grothendieckTopology X) (ModuleCat.{max u v} k) ⥤
      SheafOfModules.{max u v} R := by
  letI := fieldScalarPresheafPullback_isRightAdjoint.{u, v} X R α
  letI := fieldScalarExtension_hasSheafify.{u, v} X
  letI := fieldScalarExtension_wEqualsLocallyBijective.{u, v} X
  exact sheafToPresheaf _ _ ⋙ modulePresheafToConstantModules X ⋙
    PresheafOfModules.pullback.{max u v} (fieldScalarPresheafRingMap X R α) ⋙
      PresheafOfModules.sheafification.{max u v} (𝟙 R.obj)

end SheafOfModules
