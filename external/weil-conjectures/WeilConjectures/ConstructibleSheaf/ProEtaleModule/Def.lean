/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal

/-!

# Constructible sheaves of modules on the pro-étale site

Let `A` be a closed symmetric monoidal Grothendieck abelian category, `X` a scheme and `R` a
ring object of `Sheaf (Scheme.ProEt.topology X) A`, so that `R`-module objects are the sheaves of
`R`-modules on `X_proét`.

## Local finite presentation

`ProEtale.IsLocallyFinitelyPresented R M`: there is a pro-étale cover `{Uᵢ ⟶ X}` with
`M|_{Uᵢ}` finitely presented, i.e. the cokernel of a morphism
`(R|_{Uᵢ})^{mᵢ} ⟶ (R|_{Uᵢ})^{nᵢ}` of free modules of finite rank. Torsion is allowed.

## Constructibility

This part follows the definitions in **Section 6.8** of
*Bhargav Bhatt and Peter Scholze, The pro-étale topology for schemes*

Constructibility is defined with respect to a finite stratification `X = ∐ₐ Xₐ` by locally
closed subschemes with constructible underlying subsets, using the existing notion
`Scheme.Stratification` (`ConstructibleSheaf.Defs`);
restriction to a stratum is the pullback along its immersion `Xₐ ⟶ X`. Restriction along a
morphism `g` of schemes (to a stratum, or to a member of a pro-étale cover) uses only that the
pullback `g^*` of pro-étale sheaves is lax monoidal (`ProEtale.monoidal_upperStar`): it
sends `R` to a ring object `g^* R` and `R`-modules to `g^* R`-modules (`Functor.mapMod`).

`ProEtale.IsConstructibleModuleObject R M`: there is a stratification such that for each
stratum `Xₐ`, `M|_{Xₐ}` is pro-étale locally finitely presented over `R|_{Xₐ}`. For
`R = 𝒪_{E,X}` these are the constructible `𝒪_E`-sheaves; for `R = E_X` (with `E` a field)
they are the constructible `E`-sheaves, lisse on the strata.

-/

@[expose] public section

universe u' u

open CategoryTheory MonoidalCategory MonObj Limits

open scoped Obj

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]

section Local

variable {X : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology X) A) [MonObj R]

/-- A sheaf of `R`-modules on `X_proét` is *locally finitely presented* if there is a pro-étale
cover `{Uᵢ ⟶ X}` such that each `M|_{Uᵢ}` is the cokernel of a morphism
`(R|_{Uᵢ})^m ⟶ (R|_{Uᵢ})^n` of free modules of finite rank. -/
def IsLocallyFinitelyPresented (M : Mod (Sheaf (Scheme.ProEt.topology X) A) R) : Prop :=
  ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒰.I₀,
    Mod.IsFinitelyPresented ((ProEtale.upperStar A (𝒰.f i)).obj R)
      (((ProEtale.upperStar A (𝒰.f i)).mapMod R).obj M)

end Local

section Constructible

variable {X : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology X) A) [MonObj R]

/-- A sheaf of `R`-modules `C` on `X_proét` is *constructible* if there is a finite
stratification `X = ∐ₐ Xₐ` into constructible locally closed subsets such that for every
stratum `Xₐ`, `C|_{Xₐ}` is pro-étale locally finitely presented over `R|_{Xₐ}`.

For `R = 𝒪_{E,X}` these are the constructible `𝒪_E`-sheaves. For `R = E_X` these are the
constructible `E`-sheaves, i.e. the sheaves whose restrictions to the strata of a
stratification are lisse. -/
def IsConstructibleModuleObject (M : Mod (Sheaf (Scheme.ProEt.topology X) A) R) : Prop :=
  ∃ S : Scheme.Stratification X, ∀ a : Fin S.n,
    IsLocallyFinitelyPresented ((ProEtale.upperStar A (S.immersion a)).obj R)
      (((ProEtale.upperStar A (S.immersion a)).mapMod R).obj M)

end Constructible

end AlgebraicGeometry.ProEtale
