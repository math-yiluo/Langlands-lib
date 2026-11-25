/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek

/-!

# Derived Upper Shriek

The exceptional inverse image `Rf^!` along a morphism `f : X ⟶ Y` admitting a compactification
is *constructed* here out of the two halves of the derived lower shriek
`Rf_! = Di_! ⋙ Rg_*` attached to a compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`:

`Rf^! := Rg^! ⋙ Di^*`,

where `Rg^!` is a chosen right adjoint of the derived pushforward `Rg_*` along the *proper*
morphism `g`, and `Di^*` is the levelwise pullback along the open immersion `i`, which is right
adjoint to `Di_!` by `Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction`. The
adjunction `Rf_! ⊣ Rf^!` is then the composite of these two adjunctions. The only input is the
hypothesis that `Rg_*` is a left adjoint for the proper map `g` of the compactification; then
`Rf_!` is a left adjoint.

`Rf^!` is only defined on the unbounded derived categories: it does not preserve bounded
below objects in general, so it does not restrict to `D⁺`.

# Main Results

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekOfCompactification` : `Rf^!` with respect to
  a compactification `c`, with scoped notation `Rf^!(c)[A]`.

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekOfCompactificationAdjunction` : the
  adjunction `Rf_!(c)[A] ⊣ Rf^!(c)[A]`.

- `AlgebraicGeometry.Etale.rightDerivedUpperShriek` : `Rf^! : D(Y_ét) ⥤ D(X_ét)` for the
  chosen compactification, with scoped notation `R(f)^![A]`.

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekAdjunction` : the adjunction `Rf_! ⊣ Rf^!`
  on the unbounded derived categories.

- `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriek` : `Rf_!` is a left adjoint
  on `D(X_ét)`, a consequence of the previous item.

## Implementation notes

* That `Rg_*` is a left adjoint is a hypothesis, not an instance: for an arbitrary Grothendieck
  abelian `A` it is not known. For finite coefficients `ModuleCat Λ` it is the instance
  `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerStar_of_isProper`, proved by Brown
  representability in `WeilConjectures.SixFunctors.Etale.Derived.UpperShriek`.
* `Rg^!` for proper `g` is `Functor.rightAdjoint`, i.e. an arbitrary choice of right adjoint
  extracted from the hypothesis, not a construction. Only the adjunction
  `Adjunction.ofIsLeftAdjoint` should be used about it. The composite `Rf^!` is a construction
  out of it and `Di^*`.
* The derived adjunction `Di_! ⊣ Di^*` goes through the total left derived functor of `i_!`,
  which is why the K-flat hypotheses on the coefficient category `A` of
  `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek` are needed for the
  adjunctions of this file, though not for the definition of `Rf^!` itself.
* There is no underived `f^!`, but the notation still carries the `R` of `R(f)_![A]` and
  `R((g)_*[A])`, to mark that it lives on derived categories rather than on sheaves.

## TODO

* The composition `R(f ≫ g)^! ≅ R(g)^! ⋙ R(f)^!`, from the corresponding compatibility
  of `Rf_!`.
* For `f` étale, `Rf^! = f^*`; for `f` proper, `Rf^!` is right adjoint to `Rf_*`.

-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits

open scoped CategoryTheory.Functor
open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

namespace Etale.CompactificationUpperShriek

section OfCompactification

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
  [((c.g)_*[A]).rightDerivedFunctor.IsLeftAdjoint]

/-- The exceptional inverse image `Rf^! : D(Y_ét) ⥤ D(X_ét)` attached to a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`, on the unbounded derived categories of étale sheaves: a chosen
right adjoint `Rg^!` of the derived pushforward `Rg_*` along the proper `g`, followed by the
levelwise pullback `Di^*` along the open immersion `i`. -/
noncomputable def rightDerivedUpperShriekOfCompactification :
    DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  ((c.g)_*[A]).rightDerivedFunctor.rightAdjoint ⋙ D((c.i)^*[A])

@[inherit_doc rightDerivedUpperShriekOfCompactification]
scoped notation "Rf^!("c")[" A "]" =>
  rightDerivedUpperShriekOfCompactification A c

end OfCompactification

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
  [(((HasCompactification.compactification f).g)_*[A]).rightDerivedFunctor.IsLeftAdjoint]

section Unbounded

/-- The exceptional inverse image `Rf^! : D(Y_ét) ⥤ D(X_ét)` along a morphism `f : X ⟶ Y`
admitting a compactification, on the unbounded derived categories of étale sheaves: the
functor `rightDerivedUpperShriekOfCompactification` attached to the chosen compactification
`HasCompactification.compactification f`. -/
noncomputable def rightDerivedUpperShriek :
    DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  Rf^!(HasCompactification.compactification f)[A]

@[inherit_doc rightDerivedUpperShriek]
scoped notation "R(" f ")^![" A "]" =>
  rightDerivedUpperShriek A f

end Unbounded

section Adjunction

/- The K-flat resolution package on the coefficient category `A`, needed for the derived
adjunction `Di_! ⊣ Di^*` along the open immersion of a compactification, see
`Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction`. -/
variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The adjunction `Rf_! ⊣ Rf^!` attached to a compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`:
the composite of the derived adjunction `Di_! ⊣ Di^*` along the open immersion `i` and of the
adjunction `Rg_* ⊣ Rg^!` along the proper `g`. -/
noncomputable def rightDerivedUpperShriekOfCompactificationAdjunction {f : X ⟶ Y}
    (c : Compactification f) [((c.g)_*[A]).rightDerivedFunctor.IsLeftAdjoint] :
    Rf_!(c)[A] ⊣ Rf^!(c)[A] :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction A c.i).comp
    (Adjunction.ofIsLeftAdjoint _)

/-- The adjunction `Rf_! ⊣ Rf^!` on the unbounded derived categories of étale sheaves. -/
noncomputable def rightDerivedUpperShriekAdjunction : R(f)_![A] ⊣ R(f)^![A] :=
  rightDerivedUpperShriekOfCompactificationAdjunction A (HasCompactification.compactification f)

/-- The derived lower shriek `Rf_! : D(X_ét) ⥤ D(Y_ét)` is a left adjoint, its right adjoint
being `R(f)^![A]`. -/
instance isLeftAdjoint_rightDerivedLowerShriek : (R(f)_![A]).IsLeftAdjoint :=
  (rightDerivedUpperShriekAdjunction A f).isLeftAdjoint

instance : (R(f)^![A]).IsRightAdjoint :=
  (rightDerivedUpperShriekAdjunction A f).isRightAdjoint

end Adjunction

end Etale.CompactificationUpperShriek

end AlgebraicGeometry
