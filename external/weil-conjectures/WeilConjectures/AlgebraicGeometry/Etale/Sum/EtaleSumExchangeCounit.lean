/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalizationDataSupplement
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumExchangeConstantIso
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate
import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumExchangeConstants

/-! # The specified sum exchange preserves evaluation

Source: Stacks Project, Etale Cohomology, Tag 03S6 (lemma-shriek-base-change),
Categories, Tags 0B65 and 0DV0, and Derived Categories, Tag 015F
(blueprint: lem-pur-etale-sum-exchange-counit).

All functors act on constant-A module sheaves on ordinary small etale sites. The chosen
fiber product is `pullback w e`; its projections are e' = fst and w' = snd. This is the
canonical presentation of U times_X X' used by the recorded base-change map.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private lemma sumInverseMateComponent
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    {G : C ⥤ E} {H : D ⥤ F} (a : L ⊣ R) (a' : L' ⊣ R')
    (χ : R ⋙ G ⟶ H ⋙ R') (M : C) :
    ((mateEquiv a a').symm (TwoSquare.mk _ _ _ _ χ)).app M =
      L'.map (G.map (a.unit.app M)) ≫ L'.map (χ.app (L.obj M)) ≫
        a'.counit.app (H.obj (L.obj M)) := by
  simp [mateEquiv]

/-- The specified sheaf comparison is the inverse mate of the pullback square, its
component formula preserves the sum counit, and its inverse descends to the specified
sum exchange preserving evaluation on every unbounded derived object. The last equation
says that the derived pullback square at A_X is the identity under the canonical constants.
Source: Stacks Project, Etale Cohomology, Tag 03S6 (lemma-shriek-base-change),
Categories, Tags 0B65 and 0DV0, Derived Categories, Tag 015F, and Sites, Tag 0H7J
(blueprint: lem-pur-etale-sum-exchange-counit).

Proof:
1. Conjugate the specified base-change map using the composite adjunctions. The
iterated-mates identity identifies its conjugate with that of the inverse mate of
`squareUpperStarIso`; injectivity gives equality of these two sheaf maps.
2. The inverse-mate component formula and its counit identity give the next two equations.
3. Exact derivation preserves inverse isomorphisms, identifying the specified derived
exchange with the inverse derived square of the sheaf base-change map.
4. Apply the proved exact-localization inverse-mate theorem. Its localized adjunctions
are the specified derived sum/restriction adjunctions, so the inverse-mate counit identity
holds at every unbounded derived object.
5. Constant-sheaf composition coherence gives the commuting sheaf constant square.
Compatibility of exact derivation with the degree-zero embedding, followed by naturality
of its single-functor comparison, transports this equation to the required derived square.
-/
theorem etaleSumExchangeCounit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X X' : Scheme.{u}} (e : U ⟶ X) (w : X' ⟶ X)
    [Etale e] [IsSeparated e] [QuasiCompact e]
    [IsNoetherian U] [IsNoetherian X] [IsNoetherian X'] :
    etaleLowerShriekBaseChangeMap A w e =
      ((mateEquiv
        (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance)
        (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
          (pullback.fst w e) inferInstance)).symm
        (TwoSquare.mk _ _ _ _
          (squareUpperStarIso (ModuleCat.{u + 1} A)
            (IsPullback.of_hasPullback w e).toCommSq).hom)) ∧
    (∀ M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A),
      (etaleLowerShriekBaseChangeMap A w e).app M =
        (etaleLowerShriek (ModuleCat.{u + 1} A) (pullback.fst w e) inferInstance).map
          ((upperStar (ModuleCat.{u + 1} A) (pullback.snd w e)).map
            ((etaleLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} A) e inferInstance).unit.app M)) ≫
        (etaleLowerShriek (ModuleCat.{u + 1} A) (pullback.fst w e) inferInstance).map
          ((squareUpperStarIso (ModuleCat.{u + 1} A)
            (IsPullback.of_hasPullback w e).toCommSq).hom.app
              ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M)) ≫
        (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
          (pullback.fst w e) inferInstance).counit.app
            ((upperStar (ModuleCat.{u + 1} A) w).obj
              ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M))) ∧
    (∀ N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A),
      (etaleLowerShriekBaseChangeMap A w e).app
          ((upperStar (ModuleCat.{u + 1} A) e).obj N) ≫
        (upperStar (ModuleCat.{u + 1} A) w).map
          ((etaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) e inferInstance).counit.app N) =
      (etaleLowerShriek (ModuleCat.{u + 1} A) (pullback.fst w e) inferInstance).map
          ((squareUpperStarIso (ModuleCat.{u + 1} A)
            (IsPullback.of_hasPullback w e).toCommSq).hom.app N) ≫
        (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
          (pullback.fst w e) inferInstance).counit.app
            ((upperStar (ModuleCat.{u + 1} A) w).obj N)) ∧
    exactEtaleSumExchange A e w =
      (Functor.mapDerivedCategorySquareIso
        (@asIso _ _ _ _ (etaleLowerShriekBaseChangeMap A w e)
          (isIso_etaleLowerShriekBaseChangeMap A w e))).symm ∧
    (∀ K : DerivedCategoryModule A X,
      (exactEtaleSumExchange A e w).inv.app
          ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K) ≫
        (upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory.map
          ((derivedEtaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) e inferInstance).counit.app K) =
      (etaleLowerShriek (ModuleCat.{u + 1} A)
          (pullback.fst w e) inferInstance).mapDerivedCategory.map
          ((Functor.mapDerivedCategorySquareIso
            (squareUpperStarIso (ModuleCat.{u + 1} A)
              (IsPullback.of_hasPullback w e).toCommSq)).hom.app K) ≫
        (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
          (pullback.fst w e) inferInstance).counit.app
            ((upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory.obj K)) ∧
    (Functor.mapDerivedCategorySquareIso
        (squareUpperStarIso (ModuleCat.{u + 1} A)
          (IsPullback.of_hasPullback w e).toCommSq)).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
            (ModuleCat.of A A))) ≫
      (upperStar (ModuleCat.{u + 1} A) (pullback.fst w e)).mapDerivedCategory.map
        (etaleSumExchangeConstantIso A w).hom ≫
      (etaleSumExchangeConstantIso A (pullback.fst w e)).hom =
    (upperStar (ModuleCat.{u + 1} A) (pullback.snd w e)).mapDerivedCategory.map
        (etaleSumExchangeConstantIso A e).hom ≫
      (etaleSumExchangeConstantIso A (pullback.snd w e)).hom := by
  let B := ModuleCat.{u + 1} A
  let a := etaleLowerShriekUpperStarAdjunction B e inferInstance
  let a' := etaleLowerShriekUpperStarAdjunction B (pullback.fst w e) inferInstance
  let b := upperStarLowerStarAdjunction B (pullback.snd w e)
  let b' := upperStarLowerStarAdjunction B w
  let χ := squareUpperStarIso B (IsPullback.of_hasPullback w e).toCommSq
  have hm : etaleLowerShriekBaseChangeMap A w e =
      ((mateEquiv a a').symm (TwoSquare.mk _ _ _ _ χ.hom)) := by
    apply (conjugateEquiv (a.comp b') (b.comp a')).injective
    change (conjugateEquiv (a.comp b') (b.comp a'))
        ((conjugateEquiv (a.comp b') (b.comp a')).symm
          (baseChangeMap B (IsPullback.of_hasPullback w e).toCommSq)) = _
    rw [Equiv.apply_symm_apply]
    rw [← iterated_mateEquiv_conjugateEquiv a a' b b']
    rw [Equiv.apply_symm_apply]
    rfl
  have hd : exactEtaleSumExchange A e w =
      (Functor.mapDerivedCategorySquareIso
        (@asIso _ _ _ _ (etaleLowerShriekBaseChangeMap A w e)
          (isIso_etaleLowerShriekBaseChangeMap A w e))).symm := by
    apply Iso.ext
    simp only [exactEtaleSumExchange, Functor.mapDerivedCategorySquareIso,
      Iso.trans_hom, Iso.symm_hom, Iso.trans_inv]
    rw [Functor.mapDerivedCategoryNatIso_symm]
    simp only [Iso.symm_inv, Category.assoc]
  refine ⟨hm, ?_, ?_, hd, ?_, ?_⟩
  · intro M
    rw [hm]
    exact sumInverseMateComponent a a' χ.hom M
  · intro N
    rw [hm]
    exact (mateEquiv_counit_symm a a' (TwoSquare.mk _ _ _ _ χ.hom) N).symm
  · intro K
    let : IsIso (etaleLowerShriekBaseChangeMap A w e) :=
      isIso_etaleLowerShriekBaseChangeMap A w e
    have : IsIso ((mateEquiv a a').symm (TwoSquare.mk _ _ _ _ χ.hom)) := by
      rw [← hm]
      exact isIso_etaleLowerShriekBaseChangeMap A w e
    have hloc := (exact_localization_inverse_mate a a' χ).2.1
    have hi : asIso ((mateEquiv a a').symm (TwoSquare.mk _ _ _ _ χ.hom)) =
        asIso (etaleLowerShriekBaseChangeMap A w e) := by
      apply Iso.ext
      exact hm.symm
    rw [hi] at hloc
    have hc := mateEquiv_counit_symm
      (exactLocalizationDerivedAdjunction a) (exactLocalizationDerivedAdjunction a')
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso χ).hom) K
    rw [hloc] at hc
    rw [hd]
    exact hc.symm
  · exact etaleSumExchangeConstantSquare A e w

end AlgebraicGeometry.Etale
