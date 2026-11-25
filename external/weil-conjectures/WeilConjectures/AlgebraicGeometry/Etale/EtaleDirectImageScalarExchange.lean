/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement

import WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackComposition
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
import all WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement

/-!
# Scalar extension respects ordinary etale direct-image exchange

Source: Stacks Project, sites-cohomology.tex, Tag 0E47,
`remark-compose-base-change-horizontal`, with Tag 07A7, `remark-base-change`
(blueprint: lem-pur-etale-direct-image-scalar-exchange).

The scalar functor is `scalarExtension`; the K-flat-normalized pullback comparison
is `properOpenCoefficientPullbackIso`, the canonical exactness transport of
`scalarPullbackIso`. The map chi is the existing `scalarMate`: transporting its
canonical geometric adjunction along the same exactness isomorphism identifies its
adjunct with scalar extension of the counit after this pullback comparison.
The exchange is the specified `exactDerivedBaseChangeMap`.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

private theorem coefficientMate_mapCounit
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W T : Scheme.{u}} (v : W ⟶ T)
    (M : DerivedCategoryModule A W) :
    (upperStar (ModuleCat.{u + 1} B) v).mapDerivedCategory.map ((scalarMate φ v).app M) ≫
        ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) v).counit.app
          ((scalarExtension φ W).obj M)) =
      (properOpenCoefficientPullbackIso φ v).hom.app
          (((lowerStar (ModuleCat.{u + 1} A) v).rightDerivedFunctor).obj M) ≫
        (scalarExtension φ W).map
          ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).counit.app M) := by
  rw [mapDerivedUpperStarLowerStarAdjunction_eq,
    mapDerivedUpperStarLowerStarAdjunction_eq]
  have hm := mateEquiv_counit
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) v)
    (TwoSquare.mk _ _ _ _ (scalarPullbackIso φ v).hom) M
  apply (cancel_epi
    ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) v).hom.app
      ((scalarExtension φ T).obj
        (((lowerStar (ModuleCat.{u + 1} A) v).rightDerivedFunctor).obj M)))).mp
  simp only [Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.comp_obj]
  rw [← reassoc_of%
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) v).hom.naturality
      ((scalarMate φ v).app M)]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [show (upperStar (ModuleCat.{u + 1} B) v).leftDerivedFunctor.map
      ((scalarMate φ v).app M) ≫
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) v).counit.app
        ((scalarExtension φ W).obj M) = _ from hm]
  simp only [properOpenCoefficientPullbackIso, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, Category.assoc, Iso.hom_inv_id_app_assoc, Functor.map_comp]
  simp [← Functor.map_comp, TwoSquare.mk]

private theorem coefficientPullback_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X' X Y' Y : Scheme.{u}}
    (h : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : CommSq h f' f g) (N : DerivedCategoryModule A Y) :
    (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} B) sq).hom.app
        ((scalarExtension φ Y).obj N) ≫
      D(upperStar (ModuleCat.{u + 1} B) h).map
        ((properOpenCoefficientPullbackIso φ f).hom.app N) ≫
      (properOpenCoefficientPullbackIso φ h).hom.app
        (D(upperStar (ModuleCat.{u + 1} A) f).obj N) =
    D(upperStar (ModuleCat.{u + 1} B) f').map
        ((properOpenCoefficientPullbackIso φ g).hom.app N) ≫
      (properOpenCoefficientPullbackIso φ f').hom.app
        (D(upperStar (ModuleCat.{u + 1} A) g).obj N) ≫
      (scalarExtension φ X').map
        ((exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom.app N) := by
  have hh := coefficientPullback_comp φ f h (h ≫ f) rfl N
  have hg := coefficientPullback_comp φ g f' (h ≫ f) sq.w.symm N
  let ch (R : Type (u + 1)) [CommRing R] :=
    Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} R) h f) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm
  let cg (R : Type (u + 1)) [CommRing R] :=
    Functor.mapDerivedCategoryNatIso
        (upperStarComp (ModuleCat.{u + 1} R) f' g (h ≫ f) sq.w) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm
  have hs (R : Type (u + 1)) [CommRing R] :
      (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} R) sq).hom =
        (cg R).inv ≫ (ch R).hom := by
    simp only [exactDerivedSquareUpperStarIso, squareUpperStarIso,
      Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
      Iso.trans_hom, Iso.symm_hom, cg, ch, Iso.trans_inv, Iso.symm_inv, Category.assoc]
  apply (cancel_epi ((cg B).hom.app ((scalarExtension φ Y).obj N))).mp
  simp only [hs, NatTrans.comp_app, ← Category.assoc, Iso.hom_inv_id_app,
    Category.id_comp]
  simp only [Category.assoc]
  rw [hh, reassoc_of% hg]
  simp only [cg, ch, ← Functor.map_comp, ← Category.assoc, Iso.hom_inv_id_app,
    Category.id_comp]

/-- Scalar extension commutes with the specified ordinary unbounded etale exchange,
naturally in the input complex.

Source: Stacks Project, sites-cohomology.tex, Tag 0E47,
`remark-compose-base-change-horizontal`, with Tag 07A7, `remark-base-change`
(blueprint: lem-pur-etale-direct-image-scalar-exchange).

Proof:
1. Apply lem-sf-scalar-pullback-composition to h followed by f and to f' followed
   by g, using their common composite h followed by f. These laws already use
   the K-flat-normalized scalar comparison transported to exact inverse image.
   The specified square comparison of definition-derived-base-change-map is the inverse
   of the second path's compositor followed by the first path's compositor.
   Cancel the second compositor and use the two composition laws to obtain the
   coefficient/pullback cube.
2. The definition of scalarMate and def-weil-pbc-adjunction-mate say that its
   transpose is lambda followed by scalar extension of the A-counit. The
   definition of exactDerivedBaseChangeMap similarly says that its transpose is
   the square comparison followed by pullback of the geometric counit. The
   canonical derived adjunctions are those of definition-projection-formula-map--1,
   transported to exact termwise inverse image.
3. Transpose the left-hand composite under the f'-adjunction with B coefficients.
   Counit naturality, the exchange transpose formula, square naturality, and the
   scalar-mate transpose formula rewrite it as Q(h_A^*(epsilon_f)) after the
   h/f path of the coefficient/pullback cube. Naturality of lambda_h is the last
   rewrite; no invertibility of a direct-image comparison is used.
4. Transpose the right-hand composite under the same adjunction. Use the scalar
   transpose formula for f', naturality of lambda_f', functoriality of Q, and the
   exchange transpose formula with A coefficients. The result is the same
   Q(h_A^*(epsilon_f)) after the f'/g path of that cube.
5. Postcompose the cube identity from Step 1 with Q(h_A^*(epsilon_f)). The two
   transposes agree, so injectivity of the canonical adjunction Hom bijection
   gives the claimed equality. Every map used is natural; whiskering and
   composition therefore make the equality natural in M on the entire unbounded
   derived category, without properness, flatness or boundedness assumptions. -/
theorem exactDerivedBaseChangeMap_scalarExtension
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X' X Y' Y : Scheme.{u}}
    (h : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : ChosenCartesianSquare h f' f g) (M : DerivedCategoryModule A X) :
    D(upperStar (ModuleCat.{u + 1} B) g).map ((scalarMate φ f).app M) ≫
        (exactDerivedBaseChangeMap (ModuleCat.{u + 1} B) sq.toCommSq).app
          ((scalarExtension φ X).obj M) ≫
        R(lowerStar (ModuleCat.{u + 1} B) f').map
          ((properOpenCoefficientPullbackIso φ h).hom.app M) =
      (properOpenCoefficientPullbackIso φ g).hom.app
          (R(lowerStar (ModuleCat.{u + 1} A) f).obj M) ≫
        (scalarExtension φ Y').map
          ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app M) ≫
        (scalarMate φ f').app (D(upperStar (ModuleCat.{u + 1} A) h).obj M) := by
  let PA {S T : Scheme.{u}} (v : S ⟶ T) := D(upperStar (ModuleCat.{u + 1} A) v)
  let PB {S T : Scheme.{u}} (v : S ⟶ T) := D(upperStar (ModuleCat.{u + 1} B) v)
  let QA (T : Scheme.{u}) := scalarExtension φ T
  let afA := mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  let afB := mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f
  let afA' := mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f'
  let afB' := mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f'
  let θA := exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq
  let θB := exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} B) sq.toCommSq
  let lp {S T : Scheme.{u}} (v : S ⟶ T) := (properOpenCoefficientPullbackIso φ v).hom
  let eA := exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq
  let eB := exactDerivedBaseChangeMap (ModuleCat.{u + 1} B) sq.toCommSq
  have heA : (PA f').map (eA.app M) ≫ afA'.counit.app ((PA h).obj M) =
      θA.hom.app (R(lowerStar (ModuleCat.{u + 1} A) f).obj M) ≫
        (PA h).map (afA.counit.app M) :=
    mateEquiv_counit afA afA' (TwoSquare.mk _ _ _ _ θA.hom) M
  have heB : (PB f').map (eB.app ((QA X).obj M)) ≫
      afB'.counit.app ((PB h).obj ((QA X).obj M)) =
      θB.hom.app (R(lowerStar (ModuleCat.{u + 1} B) f).obj ((QA X).obj M)) ≫
        (PB h).map (afB.counit.app ((QA X).obj M)) :=
    mateEquiv_counit afB afB' (TwoSquare.mk _ _ _ _ θB.hom) ((QA X).obj M)
  have hf := coefficientMate_mapCounit φ f M
  have hf' := coefficientMate_mapCounit φ f' ((PA h).obj M)
  have nc := afB'.counit.naturality ((lp h).app M)
  have ns := θB.hom.naturality ((scalarMate φ f).app M)
  have nh := (lp h).naturality (afA.counit.app M)
  have nf' := (lp f').naturality (eA.app M)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj] at nc ns nh nf'
  apply (afB'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  change (PB f').map ((PB g).map ((scalarMate φ f).app M)) ≫
      (PB f').map (eB.app ((QA X).obj M)) ≫
      (PB f').map (R(lowerStar (ModuleCat.{u + 1} B) f').map ((lp h).app M)) ≫
      afB'.counit.app ((QA X').obj ((PA h).obj M)) =
    (PB f').map ((lp g).app (R(lowerStar (ModuleCat.{u + 1} A) f).obj M)) ≫
      (PB f').map ((QA Y').map (eA.app M)) ≫
      (PB f').map ((scalarMate φ f').app ((PA h).obj M)) ≫
      afB'.counit.app ((QA X').obj ((PA h).obj M))
  rw [nc, reassoc_of% heB, reassoc_of% ns]
  rw [← Functor.map_comp_assoc, hf, Functor.map_comp]
  simp only [Category.assoc]
  rw [nh, hf', reassoc_of% nf']
  rw [← Functor.map_comp, heA, Functor.map_comp]
  simpa only [Category.assoc] using
    congrArg (fun t ↦ t ≫ (QA X').map ((PA h).map (afA.counit.app M)))
      (coefficientPullback_square φ h f' f g sq.toCommSq
        (R(lowerStar (ModuleCat.{u + 1} A) f).obj M))

end AlgebraicGeometry.Etale
