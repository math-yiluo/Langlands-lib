/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms

/-!
# Scalar extension along an isomorphism of ring sheaves

Source: Stacks Project, Modules on Sites, Tags 03CZ, 03EK and 03CY
(auxiliary; not a blueprint node).

The transported module functor is the existing restriction of scalars along the inverse.
The tensor convention in the existing change-of-rings construction puts the scalar first:
`s ⊗ x` represents the node's `x ⊗ s` under tensor symmetry.
-/

@[expose] public section

universe uC vC r m

open CategoryTheory
open scoped ChangeOfRings

namespace SheafOfModules

set_option backward.isDefEq.respectTransparency false

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max r m}]
  [HasWeakSheafify J AddCommGrpCat.{max r m}]
  {R S : Sheaf J CommRingCat.{r}}

/-- The canonical sheafification-unit image of a local scalar-extension pure tensor.
Source: Stacks, Tags 03EK and 03CY
(auxiliary; not a blueprint node).
This is `eta(x ⊗ s)` in the node's factor order, with no choice of a sectionwise inverse. -/
noncomputable def scalarExtensionRingIsoTmul (a : R ⟶ S)
    (M : ringedSiteModules.{max r m}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (x : M.val.obj U) (s : S.obj.obj U) :
    (changeOfRingsOfUniverses a M).val.obj U :=
  letI := siteTensor_identity_locallyInjective
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)
  letI := siteTensor_identity_locallySurjective
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)
  (((PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).unit.app
      (changeOfRingsPresheafOfUniverses a M)).app U)
        (s ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x)

end SheafOfModules
