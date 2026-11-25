/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerPulledScalar
import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerLocalizationBase

/-! # Functor comparisons for localization of finite coefficient modules

These comparisons concern inverse image and scalar restriction;
they do not involve a descended tower or choices of its level markings.

## References

* Stacks Project, Modules on Sites, Tags 03CY, 03D2 and 03D3, and Cohomology on Sites, Tag 0D6D
* Stacks Tags 03DA and 0D6D
* Stacks Project, Modules on Sites, Tags 03CY, 03D2 and 03D3 (sheafification and inverse image of
  modules), and Cohomology on Sites, Tag 0D6D (composition)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard
  lisseTowerFixedRealization constantAdicFiniteProjection localProEtaleNormalization
  adicTowerRestrictedTransition lisseTowerPulledScalarIso lisseTowerEtaleScalarIso
  constantAdicRestrictedStep

/-- Inverse image of an arbitrary semilinear finite-coefficient arrow, using the
specified coefficient mate. This is the operation used by adicTowerRestrictedTransition. -/
def lisseTowerInverseImageArrow {X Z : Scheme.{u}} (g : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    {C : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op (n + 1))))}
    {C' : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n)))}
    (t : C ⟶ (pbcDerivedRestrict (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))).obj C') :
    (adicTowerPullback g ((pbcAdicRings X d).obj (op (n + 1)))).obj C ⟶
      (pbcDerivedRestrict ((adicTowerInverseImage g).map
        (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))).obj
        ((adicTowerPullback g ((pbcAdicRings X d).obj (op n))).obj C') :=
  (adicTowerPullback g ((pbcAdicRings X d).obj (op (n + 1)))).map t ≫
    (proEtaleRingRestrictionDerivedPullback g
      ((pbcAdicRings X d).obj (op (n + 1))) ((pbcAdicRings X d).obj (op n))
      ((adicTowerInverseImage g).obj ((pbcAdicRings X d).obj (op (n + 1))))
      ((adicTowerInverseImage g).obj ((pbcAdicRings X d).obj (op n)))
      (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))
      ((adicTowerInverseImage g).map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
      (Iso.refl _) (Iso.refl _)
      ((Category.id_comp _).trans (Category.comp_id _).symm)).inv.app C'

/-- Further restriction of an inverse-image arrow to completion coefficients. -/
def lisseTowerProjectedArrow {X Z : Scheme.{u}} (g : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    {C : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op (n + 1))))}
    {C' : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n)))}
    (t : C ⟶ (pbcDerivedRestrict (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))).obj C') :=
  (pbcDerivedRestrict (constantAdicFiniteProjection g d (n + 1))).map
      (lisseTowerInverseImageArrow g d n t) ≫
    (pbcDerivedRestrictComp (constantAdicFiniteProjection g d (n + 1))
      ((adicTowerInverseImage g).map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
      (constantAdicFiniteProjection g d n)
      (constantAdicFiniteProjection_comp g d (n + 1) n (Nat.le_succ n))).hom.app
        ((adicTowerPullback g ((pbcAdicRings X d).obj (op n))).obj C')

attribute [local irreducible] pbcDerivedRestrict
  lisseTowerInverseImageArrow lisseTowerProjectedArrow

/-- Comparisons of the localization functors, including their two scalar faces.
The level comparisons are natural transformations of functors, rather than arbitrary
isomorphisms between their values. The source face contains no level marking, and
the target face contains no etale model or descent equation. -/
structure LisseTowerLocalizationComparisons
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (U : Y.ProEt) (V : U.left.ProEt) (W : Y.ProEt)
    (f : W ⟶ ProEt.mk (V.hom ≫ U.hom)) where
  pull : ∀ n : ℕ,
    DerivedCategory (pbcModules U.left
      ((adicTowerInverseImage (U.hom ≫ g)).obj ((pbcAdicRings X d).obj (op n)))) ⥤
    DerivedCategory (pbcModules W.left
      ((adicTowerInverseImage (W.hom ≫ g)).obj ((pbcAdicRings X d).obj (op n))))
  level : ∀ n : ℕ,
    localProEtaleComparison V.hom (lisseTowerEtaleRing d n) ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))
          f.left).mapDerivedCategory ⋙ lisseTowerFixedRealization (W.hom ≫ g) d n ≅
      lisseTowerEtaleRealization (U.hom ≫ g) d n ⋙ pull n
  base : ∀ n : ℕ,
    adicTowerPullback (U.hom ≫ g) ((pbcAdicRings X d).obj (op n)) ⋙ pull n ≅
      adicTowerPullback (W.hom ≫ g) ((pbcAdicRings X d).obj (op n))
  scalar : ∀ n : ℕ,
    pbcDerivedRestrict ((adicTowerInverseImage (U.hom ≫ g)).map
        (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))) ⋙ pull (n + 1) ⋙
        pbcDerivedRestrict (constantAdicFiniteProjection (W.hom ≫ g) d (n + 1)) ≅
      pull n ⋙ pbcDerivedRestrict (constantAdicFiniteProjection (W.hom ≫ g) d n)
  source : ∀ (n : ℕ) (c : LisseTowerScalarSquare (U.hom ≫ g) d n),
    LisseTowerScalarSquareSections (U.hom ≫ g) d n c →
    ∀ (C : DerivedCategory
      (Sheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1)))))
      (C' : DerivedCategory
      (Sheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))))
      (δ : C ⟶
        (normalizationRestrict U.left.smallEtaleTopology (lisseTowerEtaleQuotient d n)).obj
          C'),
    let L (j : ℕ) := (ProEtale.upperStar
      (ModuleCat.{u + 1} (lisseTowerEtaleRing d j)) f.left).mapDerivedCategory ⋙
        lisseTowerFixedRealization (W.hom ≫ g) d j
    let H (j : ℕ) := pbcDerivedRestrict (constantAdicFiniteProjection (W.hom ≫ g) d j)
    (H (n + 1)).map ((L (n + 1)).map
        (localProEtaleNormalization V.hom (lisseTowerEtaleQuotient d n) δ)) ≫
        (lisseTowerPulledScalarIso (W.hom ≫ g) f.left d n).hom.app
          ((localProEtaleComparison V.hom (lisseTowerEtaleRing d n)).obj C') ≫
        (H n).map ((level n).hom.app C') =
      (H (n + 1)).map ((level (n + 1)).hom.app C) ≫
        (pull (n + 1) ⋙ H (n + 1)).map
          ((lisseTowerEtaleRealization (U.hom ≫ g) d (n + 1)).map δ ≫
            (lisseTowerEtaleScalarIso (U.hom ≫ g) d n c).hom.app C') ≫
        (scalar n).hom.app ((lisseTowerEtaleRealization (U.hom ≫ g) d n).obj C')
  target : ∀ (n : ℕ)
    (C : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op (n + 1)))))
    (C' : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n))))
    (t : C ⟶ (pbcDerivedRestrict (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))).obj C'),
    let H (j : ℕ) := pbcDerivedRestrict (constantAdicFiniteProjection (W.hom ≫ g) d j)
    (pull (n + 1) ⋙ H (n + 1)).map
        (lisseTowerInverseImageArrow (U.hom ≫ g) d n t) ≫
        (scalar n).hom.app
          ((adicTowerPullback (U.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj C') ≫
        (H n).map ((base n).hom.app C') =
      (H (n + 1)).map ((base (n + 1)).hom.app C) ≫
        lisseTowerProjectedArrow (W.hom ≫ g) d n t

private theorem normalizedScalar_unique {X Z : Scheme.{u}} (t : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (c : LisseTowerScalarSquare t d n) (hc : LisseTowerScalarSquareSections t d n c) :
    c = lisseTowerNormalizedScalarSquare t d n := by
  have hn := lisseTowerNormalizedScalarSquare_sections t d n
  unfold LisseTowerScalarSquareSections lisseTowerScalarSquareNormalized at hc hn
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (SheafOfModules.toSheaf _).map_injective
  have h := congrArg (fun z ↦ z.app M) (hc.trans hn.symm)
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app] at h
  exact (cancel_mono _).mp h

private theorem etaleScalar_factor {X Z : Scheme.{u}} (t : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (c : LisseTowerScalarSquare t d n) :
    lisseTowerEtaleScalarIso t d n c =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (localIsomorphismComparisonCoefficients (lisseTowerEtaleQuotient d n))
          (lisseTowerFixedRealization t d (n + 1)) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (lisseTowerFixedScalarIso t d n c) ≪≫
        (Functor.associator _ _ _).symm := by
  unfold lisseTowerEtaleScalarIso lisseTowerFixedScalarIso pbcDerivedRestrict
  rfl

private theorem localization_source {X Z S T : Scheme.{u}}
    (t : Z ⟶ X) (s : T ⟶ X) (a : T ⟶ S) (b : S ⟶ Z)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (c : LisseTowerScalarSquare t d n) (hc : LisseTowerScalarSquareSections t d n c)
    (C : DerivedCategory
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1)))))
    (C' : DerivedCategory
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))))
    (δ : C ⟶ (normalizationRestrict Z.smallEtaleTopology
      (lisseTowerEtaleQuotient d n)).obj C') :
    let L (j : ℕ) := (ProEtale.upperStar
      (ModuleCat.{u + 1} (lisseTowerEtaleRing d j)) a).mapDerivedCategory ⋙
        lisseTowerFixedRealization s d j
    let H (j : ℕ) := pbcDerivedRestrict (constantAdicFiniteProjection s d j)
    (H (n + 1)).map ((L (n + 1)).map
        (localProEtaleNormalization b (lisseTowerEtaleQuotient d n) δ)) ≫
        (lisseTowerPulledScalarIso s a d n).hom.app
          ((localProEtaleComparison b (lisseTowerEtaleRing d n)).obj C') ≫
        (H n).map ((lisseTowerLocalizationLevel t s a b d n).hom.app C') =
      (H (n + 1)).map ((lisseTowerLocalizationLevel t s a b d (n + 1)).hom.app C) ≫
        (lisseTowerLocalizationPull t s a b d (n + 1) ⋙ H (n + 1)).map
          ((lisseTowerEtaleRealization t d (n + 1)).map δ ≫
            (lisseTowerEtaleScalarIso t d n c).hom.app C') ≫
        (lisseTowerLocalizationScalar t s a b d n).hom.app
          ((lisseTowerEtaleRealization t d n).obj C') := by
  rw [normalizedScalar_unique t d n c hc, etaleScalar_factor]
  have h := LisseTowerLocalizationTransport.realizationScalar_comm
    (lisseTowerFixedRealization t d n) (lisseTowerFixedRealization t d (n + 1))
    (lisseTowerLocalizationFixed s a b d n) (lisseTowerLocalizationFixed s a b d (n + 1))
    (pbcDerivedRestrict (constantAdicFiniteProjection s d n))
    (pbcDerivedRestrict (constantAdicFiniteProjection s d (n + 1)))
    (normalizationRestrict (ProEt.topology Z) (lisseTowerEtaleQuotient d n))
    (pbcDerivedRestrict ((adicTowerInverseImage t).map
      (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))))
    (lisseTowerFixedScalarIso t d n (lisseTowerNormalizedScalarSquare t d n))
    (lisseTowerLocalizationFixedScalar s a b d n)
    ((ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))) Z).mapDerivedCategory.map δ ≫
        (localIsomorphismComparisonCoefficients (lisseTowerEtaleQuotient d n)).hom.app C')
  simpa only [lisseTowerLocalizationFixed, lisseTowerLocalizationLevel,
    lisseTowerLocalizationFixedLevel, lisseTowerLocalizationScalar,
    lisseTowerLocalizationPull, lisseTowerLocalizationFixedScalar,
    localProEtaleNormalization, localProEtaleComparisonCoefficients,
    id_eq, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_map,
    Functor.comp_obj, Functor.map_comp, Functor.map_id,
    Category.id_comp, Category.comp_id, Category.assoc] using h

/-- Inverse image admits simultaneous functor comparisons compatible with finite
scalar restriction. This asserts the two faces of the coefficient cube before
applying any descended transition equation or level marking.
-/
theorem lisseTower_localization_comparisons
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (U : Y.ProEt) (V : U.left.ProEt) (W : Y.ProEt)
    (f : W ⟶ ProEt.mk (V.hom ≫ U.hom)) :
    Nonempty (LisseTowerLocalizationComparisons X Y g d U V W f) := by
  have hf : f.left ≫ (V.hom ≫ U.hom) = W.hom := f.w
  have hf' : f.left ≫ V.hom ≫ (U.hom ≫ g) = W.hom ≫ g := by
    simpa only [Category.assoc] using congrArg (fun z : W.left ⟶ Y ↦ z ≫ g) hf
  obtain ⟨e, he⟩ := lisseTower_localization_base (U.hom ≫ g) (W.hom ≫ g)
    f.left V.hom hf' d
  refine ⟨{
    pull := lisseTowerLocalizationPull (U.hom ≫ g) (W.hom ≫ g) f.left V.hom d
    level := lisseTowerLocalizationLevel (U.hom ≫ g) (W.hom ≫ g) f.left V.hom d
    base := e
    scalar := lisseTowerLocalizationScalar (U.hom ≫ g) (W.hom ≫ g) f.left V.hom d
    source := localization_source (U.hom ≫ g) (W.hom ≫ g) f.left V.hom d
    target := ?_ }⟩
  intro n C C' δ
  let P (j : ℕ) := adicTowerPullback (U.hom ≫ g) ((pbcAdicRings X d).obj (op j))
  let P' (j : ℕ) := adicTowerPullback (W.hom ≫ g) ((pbcAdicRings X d).obj (op j))
  let T (j : ℕ) := lisseTowerLocalizationPull (U.hom ≫ g) (W.hom ≫ g) f.left V.hom d j
  let H (j : ℕ) := pbcDerivedRestrict (constantAdicFiniteProjection (W.hom ≫ g) d j)
  have hn := congrArg (H (n + 1)).map ((e (n + 1)).hom.naturality δ)
  simp only [Functor.comp_map, Functor.map_comp] at hn
  unfold lisseTowerProjectedArrow lisseTowerInverseImageArrow
  change (T (n + 1) ⋙ H (n + 1)).map
      ((P (n + 1)).map δ ≫ (lisseTowerInverseImageScalar (U.hom ≫ g) d n).hom.app C') ≫
      (lisseTowerLocalizationScalar (U.hom ≫ g) (W.hom ≫ g) f.left V.hom d n).hom.app
        ((P n).obj C') ≫ (H n).map ((e n).hom.app C') = _
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [he n C']
  simp only [← Category.assoc]
  simp only [Functor.comp_map]
  erw [hn]
  simp only [Category.assoc]
  change _ = (H (n + 1)).map ((e (n + 1)).hom.app C) ≫
    ((H (n + 1)).map ((P' (n + 1)).map δ ≫
      (lisseTowerInverseImageScalar (W.hom ≫ g) d n).hom.app C') ≫ _)
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rfl

end AlgebraicGeometry.Scheme
