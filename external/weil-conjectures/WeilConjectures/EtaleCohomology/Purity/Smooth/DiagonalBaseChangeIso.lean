/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationTransport
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactificationBaseChange

/-!
# The smooth base change identification `𝒞(p₁, Δ) ≅ ω_f` under an isomorphism of squares

For an isomorphism of squares `g' ≫ f = f' ≫ g` (`g`, `g'` isomorphisms) with induced
`e : W' = X' ×_{Y'} X' ⟶ W = X ×_Y X`, and an identification `vω : Lg'^* ω_f ≅ ω_{f'}`, the
dualizing complexes of the first projections are identified through `ω_{p₁} ≅ Lp₂^* ω_f`
(`AlgebraicGeometry.Etale.dualizingComplexPullbackFstIso`), the square isomorphism
`Le^* Lp₂^* ≅ Lp₂'^* Lg'^*` and `vω` (`AlgebraicGeometry.Etale.IsoSquare.dualizingComplexFstIso`).
With this choice, the smooth base change identifications `𝒞(p₁, Δ) ≅ ω_f`
(`AlgebraicGeometry.Etale.sectionInvariantDiagonalIso`) of `f` and `f'` correspond
(`AlgebraicGeometry.Etale.IsoSquare.sectionInvariantDiagonalIso_baseChange`): this is the
coherence of the composition isomorphisms of the derived pullbacks around the sections `Δ`, `Δ'`
of `p₂`, `p₂'` (`AlgebraicGeometry.Etale.leftDerivedUpperStar_map_comp_compSectionIso`). This
discharges the hypothesis `hC` of
`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso_baseChange_of_compat`.
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

omit [IsIso g'] [IsIso g] in
/-- The second projections are compatible with `e : X' ×_{Y'} X' ⟶ X ×_Y X`. -/
lemma commSq_snd : CommSq (map sq) (pullback.snd f' f') (pullback.snd f f) g' :=
  ⟨by simp⟩

omit [IsIso g'] [IsIso g] in
/-- The diagonals are compatible with `e : X' ×_{Y'} X' ⟶ X ×_Y X`. -/
lemma diagonal_comp_map : pullback.diagonal f' ≫ map sq = g' ≫ pullback.diagonal f := by
  ext <;> simp

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (d : ℕ) [SmoothOfRelativeDimension d f]
  [SmoothOfRelativeDimension d f'] [HasCompactification f] [HasCompactification f']
  [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ X'] [QuasiSeparatedSpace Y]
  [QuasiSeparatedSpace Y'] [QuasiCompact f] [QuasiCompact f']

/-- The identification `Le^* ω_{p₁} ≅ ω_{p₁'}` induced by `vω : Lg'^* ω_f ≅ ω_{f'}` through
`ω_{p₁} ≅ Lp₂^* ω_f` (`AlgebraicGeometry.Etale.dualizingComplexPullbackFstIso`) and the square
isomorphism `Le^* Lp₂^* ≅ Lp₂'^* Lg'^*`. -/
noncomputable def dualizingComplexFstIso
    (vω : (L((g')^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex Λ f) ≅ dualizingComplex Λ f') :
    (L((map sq)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex Λ (pullback.fst f f)) ≅
      dualizingComplex Λ (pullback.fst f' f') :=
  (L((map sq)^*[ModuleCat.{u + 1} Λ])).mapIso (dualizingComplexPullbackFstIso Λ f d) ≪≫
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) (commSq_snd sq)).symm.app
      (dualizingComplex Λ f) ≪≫
    (L((pullback.snd f' f')^*[ModuleCat.{u + 1} Λ])).mapIso vω ≪≫
    (dualizingComplexPullbackFstIso Λ f' d).symm

/-- **The smooth base change identifications `𝒞(p₁, Δ) ≅ ω_f` are compatible with an
isomorphism of squares**, for the identification
`AlgebraicGeometry.Etale.IsoSquare.dualizingComplexFstIso` of the dualizing complexes of the
first projections: the hypothesis `hC` of
`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso_baseChange_of_compat`. -/
theorem sectionInvariantDiagonalIso_baseChange
    (vω : (L((g')^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex Λ f) ≅ dualizingComplex Λ f') :
    (L((g')^*[ModuleCat.{u + 1} Λ])).map (sectionInvariantDiagonalIso Λ f d).hom ≫ vω.hom =
      (derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) (isPullback_diagonal sq).toCommSq _ ≫
          (L((pullback.diagonal f')^*[ModuleCat.{u + 1} Λ])).map
            (dualizingComplexFstIso sq Λ d vω).hom) ≫
        (sectionInvariantDiagonalIso Λ f' d).hom := by
  have key := leftDerivedUpperStar_map_comp_compSectionIso (ModuleCat.{u + 1} Λ) g'
    (pullback.snd f f) (pullback.snd f' f') (map sq) (pullback.diagonal f) (pullback.diagonal f')
    (commSq_snd sq).w (diagonal_comp_map sq) (pullback.diagonal_snd f) (pullback.diagonal_snd f')
    (dualizingComplex Λ f)
  rw [← derivedSquareUpperStarIso_hom_app_eq (ModuleCat.{u + 1} Λ) (isPullback_diagonal sq).toCommSq
    _ (diagonal_comp_map sq)] at key
  have hS : (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) (commSq_snd sq)).inv.app
      (dualizingComplex Λ f) =
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) (map sq) (pullback.snd f f)).inv.app
        (dualizingComplex Λ f) ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) (pullback.snd f' f') g'
        (map sq ≫ pullback.snd f f) (commSq_snd sq).w).hom.app (dualizingComplex Λ f) := rfl
  rw [← hS] at key
  have hnat := (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ)
    (isPullback_diagonal sq).toCommSq).inv.naturality (dualizingComplexPullbackFstIso Λ f d).hom
  simp only [Functor.comp_map] at hnat
  have hcs := (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ) (pullback.diagonal f')
    (pullback.snd f' f') (pullback.diagonal_snd f')).hom.naturality vω.hom
  simp only [Functor.comp_map, Functor.id_map] at hcs
  simp only [sectionInvariantDiagonalIso, dualizingComplexFstIso, derivedSquareUpperStarIsoInvApp,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom, Functor.map_comp,
    Category.assoc]
  rw [← Functor.map_comp_assoc (L((pullback.diagonal f')^*[ModuleCat.{u + 1} Λ]))
      (dualizingComplexPullbackFstIso Λ f' d).inv (dualizingComplexPullbackFstIso Λ f' d).hom,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp, hcs, ← reassoc_of% hnat,
    reassoc_of% key, Iso.inv_hom_id_app_assoc]

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

/-- The exceptional base change of the dualizing complexes at the unit, for an isomorphism of
squares (an isomorphism, `g` being an open immersion). -/
noncomputable def IsoSquare.dualizingComplexIso :
    (L((g')^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex Λ f) ≅ dualizingComplex Λ f' :=
  have : IsIso (upperShriekBaseChangeMap Λ sq) :=
    isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion Λ sq
  asIso ((upperShriekBaseChangeMap Λ sq).app (constantComplex Λ Y) ≫
    (R(f')^![Λ]).map (leftDerivedUpperStarUnitIso _ g).hom)

/-- Blueprint `proposition-compatibility-purity-base-change` at the unit, for an isomorphism of
squares, reduced to the single compatibility `hε` of the composition isomorphisms
`RΔ^! ω_{p₁} ≅ Λ_X` (`AlgebraicGeometry.Etale.rightDerivedUpperShriekDualizingComplexIsoOfCompEqId`)
with the exceptional base change, for the identification
`AlgebraicGeometry.Etale.IsoSquare.dualizingComplexFstIso` of the dualizing complexes of the
first projections: the statement of
`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso_baseChange` for `g`, `g'` isomorphisms. -/
theorem dualizingComplexTwistShiftIso_baseChange_of_isIso
    (hε : (L((g')^*[ModuleCat.{u + 1} Λ])).map
          (rightDerivedUpperShriekDualizingComplexIsoOfCompEqId Λ (pullback.fst f f)
            (pullback.diagonal f) (pullback.diagonal_fst f)).hom ≫
        (leftDerivedUpperStarConstantComplexIso Λ g').hom =
      ((rightDerivedUpperShriekBaseChangeMap Λ (isPullback_diagonal sq)).app
          (dualizingComplex Λ (pullback.fst f f)) ≫
          (R(pullback.diagonal f')^![Λ]).map
            (dualizingComplexFstIso sq Λ d (IsoSquare.dualizingComplexIso Λ sq)).hom) ≫
        (rightDerivedUpperShriekDualizingComplexIsoOfCompEqId Λ (pullback.fst f' f')
          (pullback.diagonal f') (pullback.diagonal_fst f')).hom) :
    (upperShriekBaseChangeMap Λ sq).app (constantComplex Λ Y) ≫
        (R(f')^![Λ]).map (leftDerivedUpperStarUnitIso _ g).hom ≫
          (dualizingComplexTwistShiftIso Λ f' d aY').hom =
      (L((g')^*[ModuleCat.{u + 1} Λ])).map (dualizingComplexTwistShiftIso Λ f d aY).hom ≫
        (leftDerivedUpperStarTwistShiftIso Λ g' d (constantComplex Λ X)).hom ≫
          (twistShift Λ X' d).map (leftDerivedUpperStarUnitIso _ g').hom :=
  dualizingComplexTwistShiftIso_baseChange_of_isIso_of_compat Λ sq d aY aY'
    (dualizingComplexFstIso sq Λ d (IsoSquare.dualizingComplexIso Λ sq))
    (sectionInvariantDiagonalIso_baseChange sq Λ d (IsoSquare.dualizingComplexIso Λ sq)) hε

end Final

end AlgebraicGeometry.Etale
