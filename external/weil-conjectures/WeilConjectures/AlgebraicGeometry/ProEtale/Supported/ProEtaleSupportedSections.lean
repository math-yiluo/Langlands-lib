/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# The supported-kernel construction with the finite-coefficient interface

The attached legacy module imports a second copy of the star functors. This interface
uses the same kernel construction with the finite-coefficient star functors.
The kernel is taken in the functor category, so its action on morphisms is canonical.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The functor `M ↦ ker(M ⟶ j_*j^*M)`, including its canonical action on morphisms.
The kernel of the natural unit is computed objectwise. -/
noncomputable def finiteSupportedSections (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X U : Scheme.{u}} (j : U ⟶ X) :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ) ⥤
      Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ) :=
  kernel (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit

/-- The canonical kernel inclusion into the original sheaf, natural in the sheaf. -/
noncomputable def finiteSupportedSectionsι (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X U : Scheme.{u}} (j : U ⟶ X) : finiteSupportedSections Λ j ⟶ 𝟭 _ :=
  kernel.ι (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit

/-- The closed inverse image of the supported kernel: `s^!₀ = s^{-1} G_Z`.
On morphisms this applies closed inverse image to the induced kernel map. No adjunction
or constructibility assertion is included. -/
noncomputable def finiteClosedUpperShriek (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Z U : Scheme.{u}} (s : Z ⟶ X) (j : U ⟶ X) :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ) ⥤
      Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ) :=
  finiteSupportedSections Λ j ⋙ upperStar (ModuleCat.{u + 1} Λ) s

end AlgebraicGeometry.ProEtale
