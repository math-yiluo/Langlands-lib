/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerLocalizationComparisons

/-! # Normalized transitions for localized actual realizations

This is the transition-equation part of the actual localized realization.

## Implementation details

An arbitrary family of level isomorphisms need not commute with transitions, so
`lisseTower_localized_actual_normalized` is stated for the composites of `cmp.level`, the
inverse images of `e`, and `cmp.base`.

## References

* Stacks Project, Tags 03CY, 03DA and 06YY
* Stacks Project, Tags 03CY, 03DA and 0D6D
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard pbcDerivedRestrict
  lisseTowerFixedRealization constantAdicQuotientRealization constantAdicFiniteRealization
  constantAdicQuotientRightIso constantAdicFiniteProjection
  localProEtaleNormalization normalizationConstantArrow lisseTowerAlgebraArrow

private theorem transfer_normalized_square
    {C C' E : Type*} [Category C] [Category C'] [Category E]
    (R : C ⥤ C') (T : C' ⥤ E) (S : C ⥤ E) (k : R ⋙ T ≅ S)
    {x w : C'} {y z : C} {p q : E}
    (t : x ⟶ R.obj y) (e : y ⟶ z) (e' : x ⟶ w) (v : w ⟶ R.obj z)
    (b : p ⟶ T.obj x) (a : S.obj z ⟶ q)
    (left : p ⟶ S.obj y) (right : T.obj w ⟶ q)
    (hsource : left = b ≫ T.map t ≫ k.hom.app y)
    (ht : t ≫ R.map e = e' ≫ v)
    (htarget : T.map v ≫ k.hom.app z ≫ a = right) :
    left ≫ S.map e ≫ a = b ≫ T.map e' ≫ right := by
  calc
    _ = b ≫ T.map t ≫ k.hom.app y ≫ S.map e ≫ a := by
      rw [hsource]
      simp only [Category.assoc]
    _ = b ≫ T.map t ≫ T.map (R.map e) ≫ k.hom.app z ≫ a := by
      have hn := k.hom.naturality e
      change T.map (R.map e) ≫ k.hom.app z = k.hom.app y ≫ S.map e at hn
      rw [← Category.assoc (k.hom.app y), ← hn]
      simp only [Category.assoc]
    _ = b ≫ T.map (t ≫ R.map e) ≫ k.hom.app z ≫ a := by
      rw [T.map_comp]
      simp only [Category.assoc]
    _ = b ≫ T.map (e' ≫ v) ≫ k.hom.app z ≫ a := by rw [ht]
    _ = b ≫ T.map e' ≫ right := by
      rw [T.map_comp]
      simpa only [Category.assoc] using
        congrArg (fun r ↦ b ≫ T.map e' ≫ r) htarget

/-- The localized comparisons constructed from one coherent functor comparison satisfy
normalized transition compatibility. -/
theorem lisseTower_localized_actual_normalized
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (M : AdicTower X d)
    (U : Y.ProEt) (V : U.left.ProEt) (W : Y.ProEt)
    (f : W ⟶ ProEt.mk (V.hom ≫ U.hom))
    (cmp : LisseTowerLocalizationComparisons X Y g d U V W f)
    (D : ∀ n : ℕ, DerivedCategory
      (Sheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))))
    (c : ∀ n : ℕ, LisseTowerScalarSquare (U.hom ≫ g) d n)
    (hc : ∀ n : ℕ, LisseTowerScalarSquareSections (U.hom ≫ g) d n (c n))
    (δ : ∀ n : ℕ, D (n + 1) ⟶
      (normalizationRestrict U.left.smallEtaleTopology (lisseTowerEtaleQuotient d n)).obj
        (D n))
    (e : ∀ n : ℕ, (lisseTowerEtaleRealization (U.hom ≫ g) d n).obj (D n) ≅
      (adicTowerPullback (U.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj (M.level n))
    (hδ : ∀ n : ℕ,
      (lisseTowerEtaleRealization (U.hom ≫ g) d (n + 1)).map (δ n) ≫
          (lisseTowerEtaleScalarIso (U.hom ≫ g) d n (c n)).hom.app (D n) ≫
          (pbcDerivedRestrict ((adicTowerInverseImage (U.hom ≫ g)).map
            (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))).map (e n).hom =
        (e (n + 1)).hom ≫
          adicTowerRestrictedTransition d (U.hom ≫ g) M (n + 1) n (Nat.le_succ n)) :
    ∀ (n : ℕ),
    let L (j : ℕ) := (ProEtale.upperStar
      (ModuleCat.{u + 1} (lisseTowerEtaleRing d j)) f.left).mapDerivedCategory ⋙
        lisseTowerFixedRealization (W.hom ≫ g) d j
    let H (k : ℕ) := pbcDerivedRestrict (constantAdicFiniteProjection (W.hom ≫ g) d k)
    let actual (j : ℕ) := (cmp.level j).app (D j) ≪≫
      (cmp.pull j).mapIso (e j) ≪≫ (cmp.base j).app (M.level j)
    (H (n + 1)).map ((L (n + 1)).map
      (localProEtaleNormalization V.hom (lisseTowerEtaleQuotient d n) (δ n))) ≫
      (lisseTowerPulledScalarIso (W.hom ≫ g) f.left d n).hom.app
        ((localProEtaleComparison V.hom (lisseTowerEtaleRing d n)).obj (D n)) ≫
      (H n).map (actual n).hom =
    (H (n + 1)).map (actual (n + 1)).hom ≫
      constantAdicRestrictedStep (W.hom ≫ g) d M n := by
  intro n
  let L (j : ℕ) := (ProEtale.upperStar
    (ModuleCat.{u + 1} (lisseTowerEtaleRing d j)) f.left).mapDerivedCategory ⋙
      lisseTowerFixedRealization (W.hom ≫ g) d j
  let H (j : ℕ) := pbcDerivedRestrict (constantAdicFiniteProjection (W.hom ≫ g) d j)
  let T := cmp.pull (n + 1) ⋙ H (n + 1)
  let R := pbcDerivedRestrict ((adicTowerInverseImage (U.hom ≫ g)).map
    (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
  let t := (lisseTowerEtaleRealization (U.hom ≫ g) d (n + 1)).map (δ n) ≫
    (lisseTowerEtaleScalarIso (U.hom ≫ g) d n (c n)).hom.app (D n)
  let b (j : ℕ) := (cmp.level j).hom.app (D j)
  let a (j : ℕ) := (cmp.base j).hom.app (M.level j)
  let actual (j : ℕ) := (cmp.level j).app (D j) ≪≫
    (cmp.pull j).mapIso (e j) ≪≫ (cmp.base j).app (M.level j)
  change (H (n + 1)).map ((L (n + 1)).map
      (localProEtaleNormalization V.hom (lisseTowerEtaleQuotient d n) (δ n))) ≫
      (lisseTowerPulledScalarIso (W.hom ≫ g) f.left d n).hom.app
        ((localProEtaleComparison V.hom (lisseTowerEtaleRing d n)).obj (D n)) ≫
      (H n).map (actual n).hom =
    (H (n + 1)).map (actual (n + 1)).hom ≫
      constantAdicRestrictedStep (W.hom ≫ g) d M n
  have htarget : T.map (adicTowerRestrictedTransition d (U.hom ≫ g) M
      (n + 1) n (Nat.le_succ n)) ≫
      (cmp.scalar n).hom.app
        ((adicTowerPullback (U.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj
          (M.level n)) ≫ (H n).map (a n) =
    (H (n + 1)).map (a (n + 1)) ≫
      constantAdicRestrictedStep (W.hom ≫ g) d M n := by
    simpa only [lisseTowerInverseImageArrow, lisseTowerProjectedArrow,
      adicTowerRestrictedTransition, constantAdicRestrictedStep, T, H, a] using
      cmp.target n (M.level (n + 1)) (M.level n)
        (adicTowerSemilinearTransition X d M.level M.normalization
          (n + 1) n (Nat.le_succ n))
  have ht : t ≫ R.map (e n).hom = (e (n + 1)).hom ≫
      adicTowerRestrictedTransition d (U.hom ≫ g) M (n + 1) n (Nat.le_succ n) := by
    simpa only [t, R, Category.assoc] using hδ n
  have hsource : (H (n + 1)).map ((L (n + 1)).map
      (localProEtaleNormalization V.hom (lisseTowerEtaleQuotient d n) (δ n))) ≫
      (lisseTowerPulledScalarIso (W.hom ≫ g) f.left d n).hom.app
        ((localProEtaleComparison V.hom (lisseTowerEtaleRing d n)).obj (D n)) ≫
      (H n).map (b n) =
    (H (n + 1)).map (b (n + 1)) ≫ T.map t ≫
      (cmp.scalar n).hom.app
        ((lisseTowerEtaleRealization (U.hom ≫ g) d n).obj (D n)) := by
    exact cmp.source n (c n) (hc n) (D (n + 1)) (D n) (δ n)
  have h := transfer_normalized_square R T (cmp.pull n ⋙ H n) (cmp.scalar n)
    t (e n).hom (e (n + 1)).hom
    (adicTowerRestrictedTransition d (U.hom ≫ g) M (n + 1) n (Nat.le_succ n))
    ((H (n + 1)).map (b (n + 1))) ((H n).map (a n)) _ _ hsource ht htarget
  simpa only [actual, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Functor.comp_map, Category.assoc, T, a, b] using h

end AlgebraicGeometry.Scheme
