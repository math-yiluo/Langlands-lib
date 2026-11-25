/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.SectionTwistShiftTransport
public import WeilConjectures.SixFunctors.Etale.Derived.VerdierDualWeil
public import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobeniusAdjunction

/-!
# Base change of the canonical orientation along an isomorphism of squares

Let `g' ≫ f = f' ≫ g` be a cartesian square with `f`, `f'` smooth separated of relative
dimension `d` and `g`, `g'` isomorphisms (for instance the geometric Frobenius square of a
smooth variety over a finite field). The diagonals `Δ`, `Δ'` and first projections `p₁`, `p₁'`
of `W = X ×_Y X` and `W' = X' ×_{Y'} X'` are compatible with the induced isomorphism
`e : W' ⟶ W`, and the resulting squares are cartesian
(`AlgebraicGeometry.Etale.IsoSquare.isPullback_diagonal`,
`AlgebraicGeometry.Etale.IsoSquare.isPullback_fst`).

The canonical orientations `θ_f : ω_f ≅ Λ_X(d)[2d]` and `θ_{f'}`
(`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso`) then correspond under
`vω : Lg'^* ω_f ≅ ω_{f'}` and `Lg'^*(Λ_X(d)[2d]) ≅ Λ_{X'}(d)[2d]`
(`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso_baseChange_of_compat`), given
* `hC`: the smooth base change identifications `𝒞(p₁, Δ) ≅ ω_f`
  (`AlgebraicGeometry.Etale.sectionInvariantDiagonalIso`) correspond under `vω` and
  `vω₁ : Le^* ω_{p₁} ≅ ω_{p₁'}`;
* `hε`: the composition isomorphisms `RΔ^! ω_{p₁} ≅ Λ_X`
  (`AlgebraicGeometry.Etale.rightDerivedUpperShriekDualizingComplexIsoOfCompEqId`) correspond
  under the exceptional base change and `vω₁`.

The remaining inputs, the base change of the purity of the diagonal and of the section
invariant construction, are
`AlgebraicGeometry.Etale.sectionInvariantTwistShiftIsoOfSection_baseChange`. This is the
geometric form of
`AlgebraicGeometry.Etale.SupportedCoefficientChange.map_dualizingComplexTwistShiftIso`; the
hypotheses `hC` and `hε` are the pasting laws of the compact-support base change for the cube
`p₂ ≫ f = p₁ ≫ f` and for the composite `Δ ≫ p₁ = 𝟙`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

namespace IsoSquare

variable {X Y X' Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  (sq : IsPullback g' f' f g) [IsIso g'] [IsIso g]

/-- The morphism `X' ×_{Y'} X' ⟶ X ×_Y X` induced by a square `g' ≫ f = f' ≫ g`. -/
noncomputable abbrev map : pullback f' f' ⟶ pullback f f :=
  pullback.map f' f' f f g' g' g sq.w.symm sq.w.symm

/-- The diagonals are compatible with `e : X' ×_{Y'} X' ⟶ X ×_Y X`, and the square is
cartesian when `g'` is an isomorphism. -/
lemma isPullback_diagonal : IsPullback g' (pullback.diagonal f') (pullback.diagonal f) (map sq) :=
  IsPullback.of_horiz_isIso ⟨by ext <;> simp⟩

/-- The first projections are compatible with `e : X' ×_{Y'} X' ⟶ X ×_Y X`, and the square is
cartesian when `g'` is an isomorphism. -/
lemma isPullback_fst : IsPullback (map sq) (pullback.fst f' f') (pullback.fst f f) g' :=
  IsPullback.of_horiz_isIso ⟨by simp⟩

end IsoSquare

section Orientation

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] {X Y X' Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g) [IsIso g'] [IsIso g] (d : ℕ)
  [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension d f'] [IsSeparated f]
  [IsSeparated f'] [HasCompactification f] [HasCompactification f'] [HasInvertibleExponent Λ X]
  [HasInvertibleExponent Λ X'] {k k' : Type u} [Field k] [Field k'] (aY : Y ⟶ Spec (.of k))
  [IsSeparated aY] [LocallyOfFiniteType aY] (aY' : Y' ⟶ Spec (.of k')) [IsSeparated aY']
  [LocallyOfFiniteType aY'] [QuasiSeparatedSpace Y] [QuasiSeparatedSpace Y'] [QuasiCompact f]
  [QuasiCompact f'] [HasInvertibleExponent Λ (pullback f f)]
  [HasInvertibleExponent Λ (pullback f' f')]

/-- **The canonical orientation is compatible with base change along an isomorphism of squares**,
given the compatibilities `hC` (smooth base change identifications `𝒞(p₁, Δ) ≅ ω_f`) and `hε`
(composition isomorphisms `RΔ^! ω_{p₁} ≅ Λ_X`). The geometric form of
`AlgebraicGeometry.Etale.SupportedCoefficientChange.map_dualizingComplexTwistShiftIso`. -/
theorem dualizingComplexTwistShiftIso_baseChange_of_compat
    (vω : (L((g')^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex Λ f) ≅ dualizingComplex Λ f')
    (vω₁ : (L((IsoSquare.map sq)^*[ModuleCat.{u + 1} Λ])).obj
        (dualizingComplex Λ (pullback.fst f f)) ≅ dualizingComplex Λ (pullback.fst f' f'))
    (hC : (L((g')^*[ModuleCat.{u + 1} Λ])).map (sectionInvariantDiagonalIso Λ f d).hom ≫ vω.hom =
      (derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ)
          (IsoSquare.isPullback_diagonal sq).toCommSq _ ≫
          (L((pullback.diagonal f')^*[ModuleCat.{u + 1} Λ])).map vω₁.hom) ≫
        (sectionInvariantDiagonalIso Λ f' d).hom)
    (hε : (L((g')^*[ModuleCat.{u + 1} Λ])).map
          (rightDerivedUpperShriekDualizingComplexIsoOfCompEqId Λ (pullback.fst f f)
            (pullback.diagonal f) (pullback.diagonal_fst f)).hom ≫
        (leftDerivedUpperStarConstantComplexIso Λ g').hom =
      ((rightDerivedUpperShriekBaseChangeMap Λ (IsoSquare.isPullback_diagonal sq)).app
          (dualizingComplex Λ (pullback.fst f f)) ≫
          (R(pullback.diagonal f')^![Λ]).map vω₁.hom) ≫
        (rightDerivedUpperShriekDualizingComplexIsoOfCompEqId Λ (pullback.fst f' f')
          (pullback.diagonal f') (pullback.diagonal_fst f')).hom) :
    (L((g')^*[ModuleCat.{u + 1} Λ])).map (dualizingComplexTwistShiftIso Λ f d aY).hom ≫
        (twistShiftConstantComplexBaseChangeIso Λ g' d).hom =
      vω.hom ≫ (dualizingComplexTwistShiftIso Λ f' d aY').hom := by
  have := SmoothOfRelativeDimension.smooth d f
  have := SmoothOfRelativeDimension.smooth d f'
  have hS := sectionInvariantTwistShiftIsoOfSection_baseChange Λ d (pullback.fst f f)
    (pullback.diagonal f) (pullback.diagonal_fst f) (pullback.fst f' f') (pullback.diagonal f')
    (pullback.diagonal_fst f') (IsoSquare.map sq) (IsoSquare.isPullback_diagonal sq) (f ≫ aY)
    (f' ≫ aY') vω₁ hε
  have hC' : (L((g')^*[ModuleCat.{u + 1} Λ])).map (sectionInvariantDiagonalIso Λ f d).inv ≫
      derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ)
          (IsoSquare.isPullback_diagonal sq).toCommSq _ ≫
        (L((pullback.diagonal f')^*[ModuleCat.{u + 1} Λ])).map vω₁.hom =
      vω.hom ≫ (sectionInvariantDiagonalIso Λ f' d).inv := by
    rw [← cancel_epi ((L((g')^*[ModuleCat.{u + 1} Λ])).map (sectionInvariantDiagonalIso Λ f d).hom),
      ← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
      reassoc_of% hC, Iso.hom_inv_id, Category.comp_id]
  simp only [dualizingComplexTwistShiftIso, Iso.trans_hom, Iso.symm_hom, Functor.map_comp,
    Category.assoc]
  rw [hS, reassoc_of% hC']

end Orientation

section Twist

variable (Λ : Type (u + 1)) [CommRing Λ] [HasTateTwist Λ] {X Y : Scheme.{u}}
  [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y]

/-- The pullback comparison `Le^*(Λ_Y(m)[2m]) ≅ Λ_X(m)[2m]` of
`AlgebraicGeometry.Etale.twistShiftConstantComplexBaseChangeIso` is the pullback of the
twist-and-shift (`AlgebraicGeometry.Etale.leftDerivedUpperStarTwistShiftIso`) followed by the
twist-and-shift of `Le^* Λ_Y ≅ Λ_X`. -/
lemma twistShiftConstantComplexBaseChangeIso_hom (e : X ⟶ Y) (m : ℤ) :
    (twistShiftConstantComplexBaseChangeIso Λ e m).hom =
      (leftDerivedUpperStarTwistShiftIso Λ e m (constantComplex Λ Y)).hom ≫
        (twistShift Λ X m).map (leftDerivedUpperStarUnitIso _ e).hom := by
  have hn := (L((e)^*[ModuleCat.{u + 1} Λ])).commShiftIso_hom_naturality
    (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) Y (tateObject Λ Y m)).hom (2 * m)
  have h := leftDerivedUpperStar_map_derivedTensorLeftUnitor_hom (A := ModuleCat.{u + 1} Λ) e
    (tateObject Λ Y m)
  rw [derivedTensor_map_app, ← leftDerivedUpperStarUnitIso_hom_eq_η] at h
  have hu : 𝟙_ _ ◁ (leftDerivedUpperStarTateObjectIso e m).hom ≫
      (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) X _).hom =
        (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) X _).hom ≫
          (leftDerivedUpperStarTateObjectIso e m).hom :=
    leftUnitor_naturality _
  have hin : (L((e)^*[ModuleCat.{u + 1} Λ])).map
        (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) Y (tateObject Λ Y m)).hom ≫
        (leftDerivedUpperStarTateObjectIso e m).hom ≫
        (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) X (tateObject Λ X m)).inv =
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) e (constantComplex Λ Y)
          (tateObject Λ Y m)).hom ≫
        _ ◁ (leftDerivedUpperStarTateObjectIso e m).hom ≫
        (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) e).hom ▷ tateObject Λ X m := by
    rw [h, Category.assoc, Category.assoc, ← reassoc_of% hu, Iso.hom_inv_id, Category.comp_id,
      whisker_exchange]
    rfl
  simp only [twistShiftConstantComplexBaseChangeIso, leftDerivedUpperStarTwistShiftIso,
    leftDerivedUpperStarTateShiftIso, twistShiftConstantComplexIso, twistShift, tateTwist,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom,
    Functor.comp_map, Functor.flip_obj_map, derivedTensor_obj_map, derivedTensor_map_app,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, ← Functor.map_comp, ← Functor.map_comp, hin, Functor.map_comp,
    Functor.map_comp]
  rfl

end Twist

section Final

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] {X Y X' Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g) [IsIso g'] [IsIso g] (d : ℕ)
  [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension d f'] [IsSeparated f]
  [IsSeparated f'] [HasCompactification f] [HasCompactification f'] [HasInvertibleExponent Λ X]
  [HasInvertibleExponent Λ X'] {k k' : Type u} [Field k] [Field k'] (aY : Y ⟶ Spec (.of k))
  [IsSeparated aY] [LocallyOfFiniteType aY] (aY' : Y' ⟶ Spec (.of k')) [IsSeparated aY']
  [LocallyOfFiniteType aY'] [QuasiSeparatedSpace Y] [QuasiSeparatedSpace Y'] [QuasiCompact f]
  [QuasiCompact f'] [HasInvertibleExponent Λ (pullback f f)]
  [HasInvertibleExponent Λ (pullback f' f')]

/-- Blueprint `proposition-compatibility-purity-base-change` at the unit, for an isomorphism of
squares: the statement of `AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso_baseChange` for
`g`, `g'` isomorphisms, given the compatibilities `hC` and `hε` of
`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso_baseChange_of_compat`, with
`vω := Lg'^* ω_f ⟶ Rf'^! Lg^* Λ_Y ≅ ω_{f'}` the exceptional base change at the unit (an
isomorphism, `g` being an open immersion). -/
theorem dualizingComplexTwistShiftIso_baseChange_of_isIso_of_compat
    (vω₁ : (L((IsoSquare.map sq)^*[ModuleCat.{u + 1} Λ])).obj
        (dualizingComplex Λ (pullback.fst f f)) ≅ dualizingComplex Λ (pullback.fst f' f'))
    (hC : (L((g')^*[ModuleCat.{u + 1} Λ])).map (sectionInvariantDiagonalIso Λ f d).hom ≫
        ((upperShriekBaseChangeMap Λ sq).app (constantComplex Λ Y) ≫
          (R(f')^![Λ]).map (leftDerivedUpperStarUnitIso _ g).hom) =
      (derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ)
          (IsoSquare.isPullback_diagonal sq).toCommSq _ ≫
          (L((pullback.diagonal f')^*[ModuleCat.{u + 1} Λ])).map vω₁.hom) ≫
        (sectionInvariantDiagonalIso Λ f' d).hom)
    (hε : (L((g')^*[ModuleCat.{u + 1} Λ])).map
          (rightDerivedUpperShriekDualizingComplexIsoOfCompEqId Λ (pullback.fst f f)
            (pullback.diagonal f) (pullback.diagonal_fst f)).hom ≫
        (leftDerivedUpperStarConstantComplexIso Λ g').hom =
      ((rightDerivedUpperShriekBaseChangeMap Λ (IsoSquare.isPullback_diagonal sq)).app
          (dualizingComplex Λ (pullback.fst f f)) ≫
          (R(pullback.diagonal f')^![Λ]).map vω₁.hom) ≫
        (rightDerivedUpperShriekDualizingComplexIsoOfCompEqId Λ (pullback.fst f' f')
          (pullback.diagonal f') (pullback.diagonal_fst f')).hom) :
    (upperShriekBaseChangeMap Λ sq).app (constantComplex Λ Y) ≫
        (R(f')^![Λ]).map (leftDerivedUpperStarUnitIso _ g).hom ≫
          (dualizingComplexTwistShiftIso Λ f' d aY').hom =
      (L((g')^*[ModuleCat.{u + 1} Λ])).map (dualizingComplexTwistShiftIso Λ f d aY).hom ≫
        (leftDerivedUpperStarTwistShiftIso Λ g' d (constantComplex Λ X)).hom ≫
          (twistShift Λ X' d).map (leftDerivedUpperStarUnitIso _ g').hom := by
  have hβ : IsIso (upperShriekBaseChangeMap Λ sq) :=
    isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion Λ sq
  have h := dualizingComplexTwistShiftIso_baseChange_of_compat Λ sq d aY aY'
    (asIso ((upperShriekBaseChangeMap Λ sq).app (constantComplex Λ Y) ≫
      (R(f')^![Λ]).map (leftDerivedUpperStarUnitIso _ g).hom)) vω₁ hC hε
  rw [twistShiftConstantComplexBaseChangeIso_hom, asIso_hom] at h
  simp only [Category.assoc] at h
  exact h.symm

end Final

end AlgebraicGeometry.Etale
