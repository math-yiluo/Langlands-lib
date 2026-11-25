/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumExtensionTensor
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocality
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement

import all WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumRightAdjointTensor
import all WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientLeftComparisonBaseChange
import all WeilConjectures.AlgebraicGeometry.Etale.Support.EtaleSupportMapCompatibility
import all WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumExtensionTensor
import all WeilConjectures.AlgebraicGeometry.SmoothPurity.ShriekTensorCompositionSupplement

set_option linter.privateModule false

/-! # The normalized projection square for etale precomposition

Source: blueprint `thm-asd-smooth-tensor.proof.md`, paragraph 3, expanded in step 3 of
lem-asd-tensor-mate-etale-precomp.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.defeqAttrib.useBackward true

universe v

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Etale

attribute [local instance] derivedBraidedCategory _root_.DerivedCategory.braidedCategory'
attribute [local irreducible] Functor.mapDerivedCategory upperStar lowerStar
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  leftDerivedUpperStarIsoMapDerivedCategory etaleLowerShriek

private lemma projection_iso
    (A : Type (v + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{v}} (f : X ⟶ Y) [HasCompactification f]
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    IsIso (compactSupportProjectionMap A f M K) := by
  have := isIso_projectionMap_of_finite A f
  rw [compactSupportProjectionMap_eq]
  infer_instance

private lemma conjugate_inverse
    {C : Type*} [Category C] {X Y Z W : C}
    (e : X ≅ Y) (d : Z ≅ W) (r : X ⟶ Z) (h : Y ⟶ W)
    (hi : e.inv ≫ r = h ≫ d.inv) : r ≫ d.hom = e.hom ≫ h := by
  apply (cancel_epi e.inv).1
  rw [← Category.assoc, hi]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.inv_hom_id_assoc]

end AlgebraicGeometry.Etale
