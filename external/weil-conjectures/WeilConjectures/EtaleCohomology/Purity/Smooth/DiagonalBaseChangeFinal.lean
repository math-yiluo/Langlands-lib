/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalPasteVert
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalPasteHoriz
public import WeilConjectures.EtaleCohomology.Purity.Smooth.IdentitySquareBaseChange
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-!
# Base change of the canonical orientation along an isomorphism of squares

Blueprint `proposition-compatibility-purity-base-change` at the unit, for an isomorphism of
cartesian squares of noetherian schemes (the Frobenius square): the statement of
`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso_baseChange` follows from the reduction
`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso_baseChange_of_isIso_of_laws` and the three
laws of the compactly supported direct image:

* `H1`, the vertical pasting of `Ex_!` along `Δ ≫ p₁ = 𝟙`
  (`AlgebraicGeometry.Etale.IsoSquare.exchangeCompCompatible_diagonal`);
* `H2`, the identity square
  (`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap_id_app_comp`);
* `H3`, the horizontal pasting of `Ex^!` along the rectangle `p₁' / f`
  (`AlgebraicGeometry.Etale.IsoSquare.dualizingComplexFstIso_hom_eq`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] {X Y X' Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g) [IsIso g'] [IsIso g] (d : ℕ)
  [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension d f'] [IsSeparated f]
  [IsSeparated f'] [HasCompactification f] [HasCompactification f'] [HasInvertibleExponent Λ X]
  [HasInvertibleExponent Λ X'] {k k' : Type u} [Field k] [Field k'] (aY : Y ⟶ Spec (.of k))
  [IsSeparated aY] [LocallyOfFiniteType aY] (aY' : Y' ⟶ Spec (.of k')) [IsSeparated aY']
  [LocallyOfFiniteType aY'] [QuasiSeparatedSpace Y] [QuasiSeparatedSpace Y'] [QuasiCompact f]
  [QuasiCompact f'] [IsNoetherian X] [IsNoetherian X']

/-- Blueprint `proposition-compatibility-purity-base-change` at the unit, for an isomorphism of
squares of noetherian schemes (the Frobenius square): the canonical orientations `θ_f`, `θ_{f'}` are
compatible with the exceptional base change and the pullback of the twist-and-shift. This is the
statement of `AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso_baseChange` for `g`, `g'`
isomorphisms. -/
theorem dualizingComplexTwistShiftIso_baseChange_of_isIso_of_isNoetherian :
    (upperShriekBaseChangeMap Λ sq).app (constantComplex Λ Y) ≫
        (R(f')^![Λ]).map (leftDerivedUpperStarUnitIso _ g).hom ≫
          (dualizingComplexTwistShiftIso Λ f' d aY').hom =
      (L((g')^*[ModuleCat.{u + 1} Λ])).map (dualizingComplexTwistShiftIso Λ f d aY).hom ≫
        (leftDerivedUpperStarTwistShiftIso Λ g' d (constantComplex Λ X)).hom ≫
          (twistShift Λ X' d).map (leftDerivedUpperStarUnitIso _ g').hom := by
  have : Smooth f := SmoothOfRelativeDimension.smooth d f
  have : Smooth f' := SmoothOfRelativeDimension.smooth d f'
  have : LocallyOfFiniteType f := inferInstance
  have : LocallyOfFiniteType f' := inferInstance
  have : IsNoetherian (pullback f f) := isNoetherian_of_locallyOfFiniteType (pullback.fst f f)
  have : IsNoetherian (pullback f' f') :=
    isNoetherian_of_locallyOfFiniteType (pullback.fst f' f')
  have : HasInvertibleExponent Λ (pullback f f) := HasInvertibleExponent.of_hom (pullback.fst f f)
  have : HasInvertibleExponent Λ (pullback f' f') :=
    HasInvertibleExponent.of_hom (pullback.fst f' f')
  exact dualizingComplexTwistShiftIso_baseChange_of_isIso_of_laws Λ sq d aY aY'
    (IsoSquare.exchangeCompCompatible_diagonal Λ sq)
    (fun K ↦ rightDerivedUpperShriekBaseChangeMap_id_app_comp Λ g' (IsoSquare.isPullback_id g') K)
    (IsoSquare.dualizingComplexFstIso_hom_eq Λ sq d)

end AlgebraicGeometry.Etale
