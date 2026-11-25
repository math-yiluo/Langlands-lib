/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableOverField
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf

public import WeilConjectures.SixFunctors.Etale.Derived.Tensor

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection

/-! # Smooth tensor duality for ordinary etale coefficients

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/thm-asd-smooth-tensor.md
(blueprint: proposition-exceptional-inverse-image-smooth-morphism).

The tensor morphism is the specified adjunction mate, with no chosen orientation.
-/

@[expose] public section

universe u u' w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The canonical derived braiding, obtained from the Koszul braiding of the homotopy
category by the derived tensor universal property. Source: blueprint
sec-smooth-purity/sk-prop-sf-cbc/thm-asd-smooth-tensor.md, the tensor mate;
(blueprint: proposition-exceptional-inverse-image-smooth-morphism). This uses the actual derived
braiding construction, not a choice of an unspecified isomorphism. -/
@[instance_reducible]
noncomputable def smoothTensorCanonicalDerivedBraiding
    (C : Type u') [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] [HasDerivedCategory.{u + 1} C] :
    BraidedCategory (_root_.DerivedCategory C) :=
  DerivedMonoidal.braidedCategory' (_root_.DerivedCategory.Qh (C := C))
    (HomotopyCategory.quasiIso C (.up ℤ))

/-- The canonical tensor morphism for the ordinary exceptional adjoint. Source: blueprint
sec-smooth-purity/sk-prop-sf-cbc/thm-asd-smooth-tensor.md, first displayed composite in
its proof (blueprint: proposition-exceptional-inverse-image-smooth-morphism).

Transpose the inverse compact-support projection formula followed by tensoring the
counit at the coefficient unit and the right unit constraint. The upstream projection
map uses the opposite order of tensor factors; the two canonical Koszul symmetries
put it in the displayed order. Its inverse is determined by that map. -/
noncomputable def smoothTensorDualityMap
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f]
    (hPF : IsIso (projectionMap (ModuleCat.{u + 1} Λ) f))
    (K : _root_.DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
      ((upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.obj K)).obj
      (dualizingComplex Λ f) ⟶ (rightDerivedUpperShriek Λ f).obj K := by
  letI := smoothTensorCanonicalDerivedBraiding (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  letI := smoothTensorCanonicalDerivedBraiding (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  let F := rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f
  let w := dualizingComplex Λ f
  let P := (upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor
  letI := hPF
  exact (rightDerivedUpperShriekAdjunction Λ f).homEquiv _ K
    (F.map (β_ (P.obj K) w).hom ≫
      inv (((projectionMap (ModuleCat.{u + 1} Λ) f).app w).app K) ≫
      (β_ (F.obj w) K).hom ≫
      ((derivedTensor (ModuleCat.{u + 1} Λ) S).obj K).map
        ((rightDerivedUpperShriekAdjunction Λ f).counit.app (𝟙_ _)) ≫
      (derivedTensorRightUnitor (ModuleCat.{u + 1} Λ) S K).hom)

end AlgebraicGeometry.Etale
