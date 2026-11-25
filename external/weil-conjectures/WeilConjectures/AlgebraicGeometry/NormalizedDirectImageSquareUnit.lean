/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.DerivedDirectImageSquareMate
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.AlgebraicGeometry.NormalizedDirectImageSquarePaste
/-! # Right-derived unit normalization of direct-image squares

Source: Stacks Project, Cohomology, Tag 0D5T.
(blueprint: lem-pc-normalized-direct-image-square-unit).
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option cleanup.letToHave false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
local instance (Z : Scheme.{u}) : Category Z.Modules :=
  inferInstanceAs (Category (SheafOfModules.{u} (moduleRings Z.toRingedSpace)))
local instance (Z : Scheme.{u}) : Abelian Z.Modules :=
  inferInstanceAs (Abelian (SheafOfModules.{u} (moduleRings Z.toRingedSpace)))
local instance (Z : Scheme.{u}) : HasDerivedCategory.{w} Z.Modules :=
  inferInstanceAs (HasDerivedCategory.{w}
    (SheafOfModules.{u} (moduleRings Z.toRingedSpace)))

local instance (Z : Scheme.{u}) : IsGrothendieckAbelian.{u} Z.Modules :=
  SheafOfModules.isGrothendieckAbelian _
local instance (Z : Scheme.{u}) : Abelian.HasKInjectiveResolutions Z.Modules :=
  Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  DerivedCategory.Qh

-- The explicit categorical carrier conversions require the larger elaboration budget.
/-- The normalized right-adjoint square is determined by the pasted right-derived
units of its two ordinary direct-image paths.
Source: Stacks Project, Cohomology, Tag 0D5T; the determining equation in
`RingedSpace.exists_derivedModuleDirectImageComposition`.
(blueprint: lem-pc-normalized-direct-image-square-unit).

Proof: The inverse composition comparison for each path is specified by its
right-derived unit equation. Postcompose that equation with the forward comparison
and cancel the inverse to obtain the forward equation. The ordinary pushforward
composition comparison is the identity on sections; its termwise and
homotopy-category maps are identities, so the pasted unit in rightDerivedFunctorCompUnit
is exactly the two successive units appearing in the chosen normalization. Between
the paths, substitution of equal scheme morphisms proves compatibility of the unit
with pushforwardCongr and the corresponding derived equality transport. Paste
these three equations: the first forward composition, the equality transport,
and the inverse second composition. Naturality moves the homotopy-category
comparison through the units, and associativity yields the displayed equation.
Natural-transformation extensionality gives the assertion. All comparisons use
the fixed common derived-category instances. The same equations hold for
identity arrows, empty schemes, zero complexes and degenerate commuting squares. -/
theorem normalizedDirectImageSquare_unit
    {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (gX : X' ⟶ X)
    (h : gX ≫ f = f' ≫ g) :
    let e₀ := Scheme.Modules.pushforwardComp gX f ≪≫
      Scheme.Modules.pushforwardCongr h ≪≫ (Scheme.Modules.pushforwardComp f' g).symm
    let e := schemeNormalizedDirectImageCompIso gX f ≪≫
      eqToIso (congrArg (fun t ↦ schemeDerivedDirectImage t) h) ≪≫
      (schemeNormalizedDirectImageCompIso f' g).symm
    Functor.rightDerivedFunctorCompUnit (Scheme.Modules.pushforward gX)
      (Scheme.Modules.pushforward f) ≫
      Functor.whiskerLeft DerivedCategory.Qh e.hom =
    Functor.whiskerRight (NatTrans.mapHomotopyCategory e₀.hom (.up ℤ))
      DerivedCategory.Qh ≫
      Functor.rightDerivedFunctorCompUnit (Scheme.Modules.pushforward f')
        (Scheme.Modules.pushforward g) := by
  dsimp only
  apply NatTrans.ext
  funext K
  have h₁ := normalizedDirectImageCompUnit gX f K
  have h₂ := normalizedDirectImageCompUnit f' g K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app]
  erw [Functor.whiskerLeft_app]
  erw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom]
  erw [NatTrans.comp_app, NatTrans.comp_app]
  simp only [eqToIso.hom]
  exact normalizedDirectImageSquare_component f f' g gX h K h₁ h₂
    (directImageSquare_unit_transport gX f f' g h K)


end AlgebraicGeometry
