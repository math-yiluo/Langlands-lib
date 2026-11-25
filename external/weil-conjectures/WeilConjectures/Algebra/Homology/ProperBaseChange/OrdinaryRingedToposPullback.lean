/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits

/-! # Ordinary tensor pullback along a ringed geometric morphism

Source: Stacks Project, Modules on Sites, Definition 03D6 (2) and Lemma 03D2
(blueprint: def-weil-pbc-ordinary-ringed-topos-pullback).

The algebraic inverse-image lift records the transported operations, and the ring map
is the structural map expressed in that lift. The construction is the existing
sheafified extension of scalars, without choosing an arbitrary module functor.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace SheafOfModules

/-- The ordinary pullback object, expressed in any algebraic inverse-image presentation.
Source: Stacks Project, Modules on Sites, Definition 03D6 (2) and Lemma 03D2
(blueprint: def-weil-pbc-ordinary-ringed-topos-pullback).

For a geometric inverse image `L`, `I` transports both ring and module operations by
finite-limit preservation. A map `c : RI ⟶ A` is the structural ring map in this
presentation. The result is exactly the sheafification of the presheaf
`U ↦ A(U) ⊗[RI(U)] I(M)(U)`, with the target-ring action on the first factor.
The compatibility with a specified ringed-topos morphism is imposed where used. -/
noncomputable def ordinaryRingedToposPullback
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {A RI : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    {L : Sheaf K (Type u) ⥤ Sheaf J (Type u)}
    (I : AlgebraicInverseImage L B RI) (c : RI ⟶ A)
    (M : ringedSiteModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B)) :
    ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A) :=
  changeOfRings.{u, u, u} (J := J) c (I.modules.obj M)

end SheafOfModules
