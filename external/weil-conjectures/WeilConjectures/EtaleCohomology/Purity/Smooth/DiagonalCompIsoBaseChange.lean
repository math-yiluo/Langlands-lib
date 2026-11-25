/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalBaseChangeIso
public import WeilConjectures.CategoryTheory.Adjunction.MateCompConjugate

/-!
# The composition isomorphism `RΔ^! ω_{p₁} ≅ Λ_X` under an isomorphism of squares

The last input of the base change of the canonical orientation along an isomorphism of squares
(`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso_baseChange_of_isIso`) is the
compatibility `hε` of `RΔ^! Rp₁^! Λ_X ≅ R(𝟙)^! Λ_X ≅ Λ_X`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekDualizingComplexIsoOfCompEqId`) with the
exceptional base change. It follows from three laws of the compactly supported direct image
(`AlgebraicGeometry.Etale.IsoSquare.compEqId_baseChange`):
* `H1`: the vertical pasting of the compact-support base change `Ex_!` along `Δ ≫ p₁ = 𝟙`, with
  respect to the composition isomorphisms
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIsoOfEq`
  (`CategoryTheory.Adjunction.ExchangeCompCompatible`);
* `H2`: the base change along the identity square is `R(𝟙)^! ≅ 𝟭`
  (`AlgebraicGeometry.Etale.rightDerivedUpperShriekIdIso`);
* `H3`: the identification `Le^* ω_{p₁} ≅ ω_{p₁'}` of
  `AlgebraicGeometry.Etale.IsoSquare.dualizingComplexFstIso` is the exceptional base change of
  `p₁` at the unit (the horizontal pasting of the exceptional base change).

The mate calculus is `CategoryTheory.Adjunction.mateEquiv_inv_comp`.
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

omit [IsIso g] in
/-- The identity square of `g'`. -/
lemma isPullback_id (g' : X' ⟶ X) [IsIso g'] : IsPullback g' (𝟙 X') (𝟙 X) g' :=
  IsPullback.of_horiz_isIso ⟨by simp⟩

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (d : ℕ) [SmoothOfRelativeDimension d f]
  [SmoothOfRelativeDimension d f'] [IsSeparated f] [IsSeparated f'] [HasCompactification f]
  [HasCompactification f'] [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ X']
  [QuasiSeparatedSpace Y] [QuasiSeparatedSpace Y'] [QuasiCompact f] [QuasiCompact f']

-- `rfl` compares the tensor unit of `constantComplex` with the one inside the definition, which
-- needs a deep (but fast: elaboration and type checking well below 0.1 s, measured) recursion.
set_option maxRecDepth 20000 in
omit [IsIso g] [IsIso g'] in
/-- The unfolding of
`AlgebraicGeometry.Etale.rightDerivedUpperShriekDualizingComplexIsoOfCompEqId`. -/
lemma compEqId_eq {V B : Scheme.{u}} (p : V ⟶ B) [HasCompactification p] (s : B ⟶ V)
    [HasCompactification s] (hs : s ≫ p = 𝟙 B) :
    rightDerivedUpperShriekDualizingComplexIsoOfCompEqId Λ p s hs =
      (conjugateIsoEquiv ((rightDerivedUpperShriekAdjunction Λ s).comp
          (rightDerivedUpperShriekAdjunction Λ p)) (rightDerivedUpperShriekAdjunction Λ (𝟙 B))
          (rightDerivedLowerShriekCompIsoOfEq Λ s p (𝟙 B) hs)).app (constantComplex Λ B) ≪≫
        (rightDerivedUpperShriekIdIso Λ B).app (constantComplex Λ B) :=
  rfl

-- the ascription compares `dualizingComplex` with `R^!` of `constantComplex` (deep, fast)
set_option maxRecDepth 20000 in
omit [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ X'] [QuasiSeparatedSpace Y]
  [QuasiSeparatedSpace Y'] [QuasiCompact f] in
/-- The pasting of the exceptional base changes along `Δ ≫ p₁ = 𝟙` at the unit, through the
conjugates of the composition isomorphisms, given the vertical pasting `H1` of `Ex_!`. -/
lemma mate_paste_unit
    (H1 : Adjunction.ExchangeCompCompatible
      (rightDerivedLowerShriekBaseChangeMap Λ (isPullback_diagonal sq))
      (rightDerivedLowerShriekBaseChangeMap Λ (isPullback_fst sq))
      (rightDerivedLowerShriekBaseChangeMap Λ (isPullback_id g'))
      (rightDerivedLowerShriekCompIsoOfEq Λ (pullback.diagonal f) (pullback.fst f f) (𝟙 X)
        (pullback.diagonal_fst f))
      (rightDerivedLowerShriekCompIsoOfEq Λ (pullback.diagonal f') (pullback.fst f' f') (𝟙 X')
        (pullback.diagonal_fst f'))) :
    (L((g')^*[ModuleCat.{u + 1} Λ])).map
        ((conjugateIsoEquiv ((rightDerivedUpperShriekAdjunction Λ (pullback.diagonal f)).comp
          (rightDerivedUpperShriekAdjunction Λ (pullback.fst f f)))
          (rightDerivedUpperShriekAdjunction Λ (𝟙 X))
          (rightDerivedLowerShriekCompIsoOfEq Λ (pullback.diagonal f) (pullback.fst f f) (𝟙 X)
            (pullback.diagonal_fst f))).inv.app (constantComplex Λ X)) ≫
      (rightDerivedUpperShriekBaseChangeMap Λ (isPullback_diagonal sq)).app
        (dualizingComplex Λ (pullback.fst f f)) ≫
      (R(pullback.diagonal f')^![Λ]).map
        ((rightDerivedUpperShriekBaseChangeMap Λ (isPullback_fst sq)).app (constantComplex Λ X)) =
      (rightDerivedUpperShriekBaseChangeMap Λ (isPullback_id g')).app (constantComplex Λ X) ≫
        (conjugateIsoEquiv ((rightDerivedUpperShriekAdjunction Λ (pullback.diagonal f')).comp
          (rightDerivedUpperShriekAdjunction Λ (pullback.fst f' f')))
          (rightDerivedUpperShriekAdjunction Λ (𝟙 X'))
          (rightDerivedLowerShriekCompIsoOfEq Λ (pullback.diagonal f') (pullback.fst f' f')
            (𝟙 X') (pullback.diagonal_fst f'))).inv.app
          ((L((g')^*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ X)) :=
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ (isPullback_diagonal sq)
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ (isPullback_fst sq)
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ (isPullback_id g')
  Adjunction.mateEquiv_inv_comp_conjugate _ _ _ _ _ _ _ _ _ _ _ H1 (constantComplex Λ X)

/-- **The composition isomorphisms `RΔ^! ω_{p₁} ≅ Λ_X` are compatible with an isomorphism of
squares**, given the vertical pasting `H1` of `Ex_!` along `Δ ≫ p₁ = 𝟙`, the identity-square
law `H2` and the comparison `H3` of the identifications of `ω_{p₁}`. -/
theorem compEqId_baseChange
    (H1 : Adjunction.ExchangeCompCompatible
      (rightDerivedLowerShriekBaseChangeMap Λ (isPullback_diagonal sq))
      (rightDerivedLowerShriekBaseChangeMap Λ (isPullback_fst sq))
      (rightDerivedLowerShriekBaseChangeMap Λ (isPullback_id g'))
      (rightDerivedLowerShriekCompIsoOfEq Λ (pullback.diagonal f) (pullback.fst f f) (𝟙 X)
        (pullback.diagonal_fst f))
      (rightDerivedLowerShriekCompIsoOfEq Λ (pullback.diagonal f') (pullback.fst f' f') (𝟙 X')
        (pullback.diagonal_fst f')))
    (H2 : ∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (rightDerivedUpperShriekBaseChangeMap Λ (isPullback_id g')).app K ≫
          (rightDerivedUpperShriekIdIso Λ X').hom.app ((L((g')^*[ModuleCat.{u + 1} Λ])).obj K) =
        (L((g')^*[ModuleCat.{u + 1} Λ])).map ((rightDerivedUpperShriekIdIso Λ X).hom.app K))
    (H3 : (dualizingComplexFstIso sq Λ d (IsoSquare.dualizingComplexIso Λ sq)).hom =
      (rightDerivedUpperShriekBaseChangeMap Λ (isPullback_fst sq)).app (constantComplex Λ X) ≫
        (R(pullback.fst f' f')^![Λ]).map (leftDerivedUpperStarConstantComplexIso Λ g').hom) :
    (L((g')^*[ModuleCat.{u + 1} Λ])).map
          (rightDerivedUpperShriekDualizingComplexIsoOfCompEqId Λ (pullback.fst f f)
            (pullback.diagonal f) (pullback.diagonal_fst f)).hom ≫
        (leftDerivedUpperStarConstantComplexIso Λ g').hom =
      ((rightDerivedUpperShriekBaseChangeMap Λ (isPullback_diagonal sq)).app
          (dualizingComplex Λ (pullback.fst f f)) ≫
          (R(pullback.diagonal f')^![Λ]).map
            (dualizingComplexFstIso sq Λ d (IsoSquare.dualizingComplexIso Λ sq)).hom) ≫
        (rightDerivedUpperShriekDualizingComplexIsoOfCompEqId Λ (pullback.fst f' f')
          (pullback.diagonal f') (pullback.diagonal_fst f')).hom := by
  have key := mate_paste_unit sq Λ H1
  have key' : (rightDerivedUpperShriekBaseChangeMap Λ (isPullback_diagonal sq)).app
        (dualizingComplex Λ (pullback.fst f f)) ≫
      (R(pullback.diagonal f')^![Λ]).map
        ((rightDerivedUpperShriekBaseChangeMap Λ (isPullback_fst sq)).app (constantComplex Λ X)) =
      (L((g')^*[ModuleCat.{u + 1} Λ])).map
          ((conjugateIsoEquiv ((rightDerivedUpperShriekAdjunction Λ (pullback.diagonal f)).comp
            (rightDerivedUpperShriekAdjunction Λ (pullback.fst f f)))
            (rightDerivedUpperShriekAdjunction Λ (𝟙 X))
            (rightDerivedLowerShriekCompIsoOfEq Λ (pullback.diagonal f) (pullback.fst f f) (𝟙 X)
              (pullback.diagonal_fst f))).hom.app (constantComplex Λ X)) ≫
        (rightDerivedUpperShriekBaseChangeMap Λ (isPullback_id g')).app (constantComplex Λ X) ≫
        (conjugateIsoEquiv ((rightDerivedUpperShriekAdjunction Λ (pullback.diagonal f')).comp
          (rightDerivedUpperShriekAdjunction Λ (pullback.fst f' f')))
          (rightDerivedUpperShriekAdjunction Λ (𝟙 X'))
          (rightDerivedLowerShriekCompIsoOfEq Λ (pullback.diagonal f') (pullback.fst f' f')
            (𝟙 X') (pullback.diagonal_fst f'))).inv.app
          ((L((g')^*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ X)) := by
    rw [← key, ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp]
  have hnat := (conjugateIsoEquiv ((rightDerivedUpperShriekAdjunction Λ (pullback.diagonal f')).comp
      (rightDerivedUpperShriekAdjunction Λ (pullback.fst f' f')))
      (rightDerivedUpperShriekAdjunction Λ (𝟙 X'))
      (rightDerivedLowerShriekCompIsoOfEq Λ (pullback.diagonal f') (pullback.fst f' f')
        (𝟙 X') (pullback.diagonal_fst f'))).inv.naturality
    (leftDerivedUpperStarConstantComplexIso Λ g').hom
  simp only [Functor.comp_map] at hnat
  have hid := (rightDerivedUpperShriekIdIso Λ X').hom.naturality
    (leftDerivedUpperStarConstantComplexIso Λ g').hom
  simp only [Functor.id_map] at hid
  rw [H3, compEqId_eq, compEqId_eq]
  simp only [Iso.trans_hom, Iso.app_hom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% key', ← reassoc_of% hnat, Iso.inv_hom_id_app_assoc, hid,
    reassoc_of% (H2 (constantComplex Λ X))]

end IsoSquare

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

open Scheme IsoSquare

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
squares (the Frobenius square): the statement of
`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso_baseChange` for `g`, `g'` isomorphisms, from
the three laws of the compactly supported direct image `H1` (vertical pasting of `Ex_!` along
`Δ ≫ p₁ = 𝟙`, `CategoryTheory.Adjunction.ExchangeCompCompatible`), `H2` (the identity square) and
`H3` (the horizontal pasting, as the comparison of the identifications of `ω_{p₁}`). -/
theorem dualizingComplexTwistShiftIso_baseChange_of_isIso_of_laws
    (H1 : Adjunction.ExchangeCompCompatible
      (rightDerivedLowerShriekBaseChangeMap Λ (isPullback_diagonal sq))
      (rightDerivedLowerShriekBaseChangeMap Λ (isPullback_fst sq))
      (rightDerivedLowerShriekBaseChangeMap Λ (isPullback_id g'))
      (rightDerivedLowerShriekCompIsoOfEq Λ (pullback.diagonal f) (pullback.fst f f) (𝟙 X)
        (pullback.diagonal_fst f))
      (rightDerivedLowerShriekCompIsoOfEq Λ (pullback.diagonal f') (pullback.fst f' f') (𝟙 X')
        (pullback.diagonal_fst f')))
    (H2 : ∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (rightDerivedUpperShriekBaseChangeMap Λ (isPullback_id g')).app K ≫
          (rightDerivedUpperShriekIdIso Λ X').hom.app ((L((g')^*[ModuleCat.{u + 1} Λ])).obj K) =
        (L((g')^*[ModuleCat.{u + 1} Λ])).map ((rightDerivedUpperShriekIdIso Λ X).hom.app K))
    (H3 : (dualizingComplexFstIso sq Λ d (IsoSquare.dualizingComplexIso Λ sq)).hom =
      (rightDerivedUpperShriekBaseChangeMap Λ (isPullback_fst sq)).app (constantComplex Λ X) ≫
        (R(pullback.fst f' f')^![Λ]).map (leftDerivedUpperStarConstantComplexIso Λ g').hom) :
    (upperShriekBaseChangeMap Λ sq).app (constantComplex Λ Y) ≫
        (R(f')^![Λ]).map (leftDerivedUpperStarUnitIso _ g).hom ≫
          (dualizingComplexTwistShiftIso Λ f' d aY').hom =
      (L((g')^*[ModuleCat.{u + 1} Λ])).map (dualizingComplexTwistShiftIso Λ f d aY).hom ≫
        (leftDerivedUpperStarTwistShiftIso Λ g' d (constantComplex Λ X)).hom ≫
          (twistShift Λ X' d).map (leftDerivedUpperStarUnitIso _ g').hom :=
  dualizingComplexTwistShiftIso_baseChange_of_isIso Λ sq d aY aY'
    (compEqId_baseChange sq Λ d H1 H2 H3)

end Final

end AlgebraicGeometry.Etale
