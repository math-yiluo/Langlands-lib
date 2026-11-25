/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Graph.EtaleGraphChosenComparisons
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalizationDataSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.AlgebraicGeometry.Proper.ProperCompactificationRawUnit
import WeilConjectures.AlgebraicGeometry.Open.OpenExchangeDerivedUnit
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationRawUnitComparison
import WeilConjectures.AlgebraicGeometry.Etale.Graph.EtaleGraphCompactificationUnit
import all WeilConjectures.AlgebraicGeometry.SmoothPurity.RightDerivedRawUnitPasting
import all WeilConjectures.AlgebraicGeometry.Exact.ExactCompactificationUnitTower

/-! # Raw-unit normalization of proper-first compact-support composition

## References

* Stacks Project, Tags 0F7B, 0F7I, 0F7J and 0D6E
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] lowerStar upperStar etaleLowerShriek openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor canonicalEtaleCompactSupportComparison
  rightDerivedLowerShriekIso unboundedEtaleLowerShriekCompIso
  Functor.mapDerivedCategoryFactorsh Functor.rightDerivedFunctorUnit
  Functor.mapDerivedCategoryNatIso
  Functor.mapDerivedCategoryCompRightDerivedFunctorUnit
  lowerStarComp openImmersionLowerShriekComp compactificationSheafToDirectImage
  NatTrans.mapHomotopyCategory etaleCompactificationGraphMap pasteDerivedTower
  Functor.rightDerivedFunctorCompIso'
  rightDerivedLowerShriekOfCompactificationCompIso
  rightDerivedLowerShriekOfCompactificationIso openImmersionLowerShriekLowerStarExchange

private lemma raw_sheaf_tower
    (A : Type (u + 1)) [CommRing A]
    {V T B : Scheme.{u}} (h : V ⟶ T) (e : T ⟶ B)
    (d : Compactification e) (c : Compactification (h ≫ d.i))
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} A))
    (ah : F ⟶ openImmersionLowerShriek (ModuleCat.{u + 1} A) c.restrict.i ⋙
      lowerStar (ModuleCat.{u + 1} A) c.restrict.g)
    (ae : G ⟶ openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i ⋙
      lowerStar (ModuleCat.{u + 1} A) d.g)
    (χ : lowerStar (ModuleCat.{u + 1} A) c.restrict.g ⋙
      openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) (pullback.fst c.g d.i) ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g)
    (hχ : ∀ M, χ.app M ≫
      (lowerStar (ModuleCat.{u + 1} A) c.g).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A)
          (pullback.fst c.g d.i)).app M) ≫
      (lowerStarComp (ModuleCat.{u + 1} A) (pullback.fst c.g d.i) c.g
        (c.restrict.g ≫ d.i) c.isPullback_restrict.w).hom.app M =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) d.i).app
          ((lowerStar (ModuleCat.{u + 1} A) c.restrict.g).obj M) ≫
        (lowerStarComp (ModuleCat.{u + 1} A) c.restrict.g d.i).hom.app M)
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    let K := ModuleCat.{u + 1} A
    let J := openImmersionLowerShriek K c.restrict.i
    let R := lowerStar K c.restrict.g
    let O := openImmersionLowerShriek K (U := c.restrict.Z) (pullback.fst c.g d.i)
    let P := lowerStar K c.g
    let S := lowerStar K d.g
    let H := openImmersionLowerShriek K c.i
    let W := lowerStar K (c.g ≫ d.g)
    let eo : H ≅ J ⋙ O := open_congr A c.restrict_i_fst.symm ≪≫
      openImmersionLowerShriekComp K c.restrict.i (pullback.fst c.g d.i)
    let ep : P ⋙ S ≅ W := lowerStarComp K c.g d.g
    let t := Functor.whiskerRight ah G ≫
      Functor.whiskerLeft J (Functor.whiskerLeft R ae) ≫
      Functor.whiskerLeft J (Functor.whiskerRight χ S) ≫
      Functor.whiskerLeft (J ⋙ O) ep.hom ≫ Functor.whiskerRight eo.inv W
    t.app M ≫ (compactificationSheafToDirectImage A (d.comp c)).app M =
      ae.app (F.obj M) ≫ (compactificationSheafToDirectImage A d).app (F.obj M) ≫
        (lowerStar K e).map
          (ah.app M ≫ (compactificationSheafToDirectImage A c.restrict).app M) ≫
        (lowerStarComp K h e).hom.app M := by
  intro K J R O P S H W eo ep t
  dsimp only [t, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp only [Category.assoc]
  refine (congrArg (fun z ↦ G.map (ah.app M) ≫
    ae.app (R.obj (J.obj M)) ≫ z)
    (canonical_sheaf_tower A h e d c χ hχ M)).trans ?_
  have ne := ae.naturality (ah.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at ne
  rw [reassoc_of% ne]
  have ni := (compactificationSheafToDirectImage A d).naturality (ah.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at ni
  rw [reassoc_of% ni, ← (lowerStar K e).map_comp_assoc]

private lemma chosen_tower_comparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {W V Y : Scheme.{u}} [IsNoetherian W] [IsNoetherian V] [IsNoetherian Y]
    (q : W ⟶ V) [IsProper q]
    (v : V ⟶ Y) [Etale v] [IsSeparated v] [QuasiCompact v]
    [HasCompactification v] [HasCompactification (q ≫ v)]
    (e : Compactification (q ≫ (HasCompactification.compactification v).i))
    (c : Compactification (q ≫ v)) :
    let B := ModuleCat.{u + 1} A
    let d := HasCompactification.compactification v
    let G := etaleLowerShriek B v inferInstance
    let γh := ((graphChosenProperComparison A q).symm ≪≫
      (rightDerivedLowerShriekIso A e.restrict).symm).hom
    let γe := (canonicalEtaleCompactSupportComparison A v d).inv
    (Functor.isoWhiskerRight (graphChosenProperComparison A q).symm
          G.mapDerivedCategory ≪≫
        Functor.isoWhiskerLeft (rightDerivedLowerShriek B q)
          (graphChosenEtaleComparison A v).symm ≪≫
        unboundedEtaleLowerShriekCompIso A q v ≪≫
        (rightDerivedLowerShriekIso A c).symm).hom =
      Functor.whiskerRight γh G.mapDerivedCategory ≫
        Functor.whiskerLeft (rightDerivedLowerShriekOfCompactification B e.restrict) γe ≫
        (rightDerivedLowerShriekOfCompactificationCompIso A d e).hom ≫
        (rightDerivedLowerShriekOfCompactificationIso A (d.comp e) c).hom := by
  intro B d G γh γe
  have hh := (unboundedEtaleCompactSupport_comparison_coherence A (q ≫ v)).2
    (d.comp e) c (HasCompactification.compactification (q ≫ v))
  have hh' : (rightDerivedLowerShriekIso A (d.comp e)).hom ≫
      (rightDerivedLowerShriekIso A c).inv =
      (rightDerivedLowerShriekOfCompactificationIso A (d.comp e) c).hom := by
    apply (cancel_mono (rightDerivedLowerShriekIso A c).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    simpa only [rightDerivedLowerShriekIso, Iso.trans_hom] using
      (congrArg Iso.hom hh).symm
  simp only [Iso.trans_hom]
  rw [unboundedEtaleLowerShriekCompIso_tower A q v d e]
  apply NatTrans.ext
  funext M
  simp only [γh, γe, graphChosenEtaleComparison, d, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.hcomp_app, Functor.map_comp, Category.assoc]
  rw [Iso.hom_inv_id_app_assoc]
  have nn := (canonicalEtaleCompactSupportComparison A v d).inv.naturality
    ((rightDerivedLowerShriekIso A e.restrict).inv.app M)
  simp only [d] at nn
  erw [← reassoc_of% nn]
  have hk := congr_app hh' M
  simp only [NatTrans.comp_app] at hk
  erw [hk]
  rfl

private def ordinaryMate
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (L : C ⥤ D) (R : D ⥤ C) (L' : E ⥤ F) (R' : F ⥤ E)
    (T : C ⥤ E) (O : D ⥤ F)
    (adj : L ⊣ R) (adj' : L' ⊣ R') (β : T ⋙ L' ⟶ L ⋙ O) :
    R ⋙ T ⟶ O ⋙ R' :=
  (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ β))

private noncomputable def ordinaryOpenExchange
    (A : Type (u + 1)) [CommRing A]
    {U V W Z : Scheme.{u}} (b : U ⟶ V) (q : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion b] [IsOpenImmersion i] (sq : IsPullback q b i p) :
    lowerStar (ModuleCat.{u + 1} A) q ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} A) i ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) b ⋙
        lowerStar (ModuleCat.{u + 1} A) p :=
  ordinaryMate (upperStar (ModuleCat.{u + 1} A) q)
    (lowerStar (ModuleCat.{u + 1} A) q) (upperStar (ModuleCat.{u + 1} A) p)
    (lowerStar (ModuleCat.{u + 1} A) p) (openImmersionLowerShriek (ModuleCat.{u + 1} A) i)
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) b)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
    (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap
      (ModuleCat.{u + 1} A) sq)).inv

attribute [local irreducible] ordinaryOpenExchange

private lemma ordinaryOpenExchange_eq
    (A : Type (u + 1)) [CommRing A]
    {U V W Z : Scheme.{u}} (b : U ⟶ V) (q : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion b] [IsOpenImmersion i] (sq : IsPullback q b i p) :
    ordinaryOpenExchange A b q p i sq =
      (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q)
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
        (TwoSquare.mk _ _ _ _ (@asIso _ _ _ _ _
          (isIso_openImmersionLowerShriekBaseChangeMap
            (ModuleCat.{u + 1} A) sq)).inv)) := by
  unfold ordinaryOpenExchange ordinaryMate
  rfl

private lemma ordinaryOpenExchange_inclusion
    (A : Type (u + 1)) [CommRing A]
    {U V W Z : Scheme.{u}} (b : U ⟶ V) (q : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion b] [IsOpenImmersion i] (sq : IsPullback q b i p)
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (ordinaryOpenExchange A b q p i sq).app M ≫
        (lowerStar (ModuleCat.{u + 1} A) p).map
          ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) b).app M) ≫
        (lowerStarComp (ModuleCat.{u + 1} A) b p (q ≫ i) sq.w).hom.app M =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app
          ((lowerStar (ModuleCat.{u + 1} A) q).obj M) ≫
        (lowerStarComp (ModuleCat.{u + 1} A) q i).hom.app M := by
  rw [ordinaryOpenExchange_eq, reassoc_of% (sheaf_exchange_inclusion A b q p i sq M)]
  simp only [squareLowerStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc]
  erw [Iso.inv_hom_id_app]
  simp only [Category.comp_id]

private lemma proper_inclusion_isIso
    (A : Type (u + 1)) [CommRing A] {W V : Scheme.{u}}
    (q : W ⟶ V) [IsProper q] (c : Compactification q) :
    IsIso (compactificationSheafToDirectImage A c) := by
  have : IsProper c.i := by
    have : IsProper (c.i ≫ c.g) := by rw [← c.comm]; infer_instance
    exact IsProper.of_comp _ c.g
  have : IsIso (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i) :=
    isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range
      (ModuleCat.{u + 1} A) c.i c.i.isClosedMap.isClosed_range
  unfold compactificationSheafToDirectImage
  infer_instance

private noncomputable def properSupportInverse
    (A : Type (u + 1)) [CommRing A] {W V : Scheme.{u}}
    (q : W ⟶ V) [IsProper q] (c : Compactification q) :
    lowerStar (ModuleCat.{u + 1} A) q ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g := by
  letI := proper_inclusion_isIso A q c
  exact (asIso (compactificationSheafToDirectImage A c)).inv

attribute [local irreducible] properSupportInverse

private lemma properSupportInverse_normalization
    (A : Type (u + 1)) [CommRing A] {W V : Scheme.{u}}
    (q : W ⟶ V) [IsProper q] (c : Compactification q) :
    properSupportInverse A q c ≫ compactificationSheafToDirectImage A c =
      𝟙 (lowerStar (ModuleCat.{u + 1} A) q) := by
  let := proper_inclusion_isIso A q c
  unfold properSupportInverse
  exact (asIso (compactificationSheafToDirectImage A c)).inv_hom_id

private noncomputable def towerSheafMap
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {W V Y : Scheme.{u}}
    [IsNoetherian W] [IsNoetherian V] [IsNoetherian Y]
    (q : W ⟶ V) [IsProper q]
    (v : V ⟶ Y) [Etale v] [IsSeparated v] [QuasiCompact v]
    [HasCompactification v] [HasCompactification (q ≫ v)]
    (d : Compactification v) (e : Compactification (q ≫ d.i)) :
    lowerStar (ModuleCat.{u + 1} A) q ⋙
        etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) e.i ⋙
        lowerStar (ModuleCat.{u + 1} A)
          (e.g ≫ d.g) := by
  let B := ModuleCat.{u + 1} A
  let J := openImmersionLowerShriek B e.restrict.i
  let R := lowerStar B e.restrict.g
  let I := openImmersionLowerShriek B d.i
  let O := openImmersionLowerShriek B (U := e.restrict.Z) (pullback.fst e.g d.i)
  let P := lowerStar B e.g
  let S := lowerStar B d.g
  let H := openImmersionLowerShriek B e.i
  let T := lowerStar B (e.g ≫ d.g)
  let F := lowerStar B q
  let G := etaleLowerShriek B v inferInstance
  let ah := properSupportInverse A q e.restrict
  let ae := etaleCompactificationGraphMap A v d
  let χ := ordinaryOpenExchange A (U := e.restrict.Z) (pullback.fst e.g d.i)
    e.restrict.g e.g d.i e.isPullback_restrict
  let eo : H ≅ J ⋙ O := open_congr A e.restrict_i_fst.symm ≪≫
    openImmersionLowerShriekComp B e.restrict.i (pullback.fst e.g d.i)
  let ep : P ⋙ S ≅ T := lowerStarComp B e.g d.g
  exact Functor.whiskerRight ah G ≫ Functor.whiskerLeft J (Functor.whiskerLeft R ae) ≫
      Functor.whiskerLeft J (Functor.whiskerRight χ S) ≫
      Functor.whiskerLeft (J ⋙ O) ep.hom ≫ Functor.whiskerRight eo.inv T

attribute [local irreducible] towerSheafMap

private lemma towerSheafMap_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {W V Y : Scheme.{u}}
    [IsNoetherian W] [IsNoetherian V] [IsNoetherian Y]
    (q : W ⟶ V) [IsProper q]
    (v : V ⟶ Y) [Etale v] [IsSeparated v] [QuasiCompact v]
    [HasCompactification v] [HasCompactification (q ≫ v)]
    (d : Compactification v) (e : Compactification (q ≫ d.i)) :
    let B := ModuleCat.{u + 1} A
    let J := openImmersionLowerShriek B e.restrict.i
    let R := lowerStar B e.restrict.g
    let O := openImmersionLowerShriek B (U := e.restrict.Z) (pullback.fst e.g d.i)
    let P := lowerStar B e.g
    let S := lowerStar B d.g
    let H := openImmersionLowerShriek B e.i
    let T := lowerStar B (e.g ≫ d.g)
    let G := etaleLowerShriek B v inferInstance
    let ah := properSupportInverse A q e.restrict
    let ae := etaleCompactificationGraphMap A v d
    let χ := ordinaryOpenExchange A (U := e.restrict.Z) (pullback.fst e.g d.i)
      e.restrict.g e.g d.i e.isPullback_restrict
    let eo : H ≅ J ⋙ O := open_congr A e.restrict_i_fst.symm ≪≫
      openImmersionLowerShriekComp B e.restrict.i (pullback.fst e.g d.i)
    let ep : P ⋙ S ≅ T := lowerStarComp B e.g d.g
    towerSheafMap A q v d e =
      Functor.whiskerRight ah G ≫ Functor.whiskerLeft J (Functor.whiskerLeft R ae) ≫
      Functor.whiskerLeft J (Functor.whiskerRight χ S) ≫
      Functor.whiskerLeft (J ⋙ O) ep.hom ≫ Functor.whiskerRight eo.inv T := by
  unfold towerSheafMap
  rfl

private lemma towerSheafMap_normalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {W V Y : Scheme.{u}}
    [IsNoetherian W] [IsNoetherian V] [IsNoetherian Y]
    (q : W ⟶ V) [IsProper q]
    (v : V ⟶ Y) [Etale v] [IsSeparated v] [QuasiCompact v]
    [HasCompactification v] [HasCompactification (q ≫ v)]
    (d : Compactification v) (e : Compactification (q ≫ d.i))
    (M : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (towerSheafMap A q v d e).app M ≫
        (compactificationSheafToDirectImage A
          (d.comp e)).app M =
      etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) v
          ((lowerStar (ModuleCat.{u + 1} A) q).obj M) ≫
        (lowerStarComp (ModuleCat.{u + 1} A) q v).hom.app M := by
  let B := ModuleCat.{u + 1} A
  let J := openImmersionLowerShriek B e.restrict.i
  let R := lowerStar B e.restrict.g
  let I := openImmersionLowerShriek B d.i
  let O := openImmersionLowerShriek B (U := e.restrict.Z) (pullback.fst e.g d.i)
  let P := lowerStar B e.g
  let S := lowerStar B d.g
  let H := openImmersionLowerShriek B e.i
  let T := lowerStar B (e.g ≫ d.g)
  let F := lowerStar B q
  let G := etaleLowerShriek B v inferInstance
  let ah := properSupportInverse A q e.restrict
  let ae := etaleCompactificationGraphMap A v d
  let χ := ordinaryOpenExchange A (U := e.restrict.Z) (pullback.fst e.g d.i)
    e.restrict.g e.g d.i e.isPullback_restrict
  let eo : H ≅ J ⋙ O := open_congr A e.restrict_i_fst.symm ≪≫
    openImmersionLowerShriekComp B e.restrict.i (pullback.fst e.g d.i)
  let ep : P ⋙ S ≅ T := lowerStarComp B e.g d.g
  have nah := properSupportInverse_normalization A q e.restrict
  have hχ (M : Sheaf e.restrict.Z.smallEtaleTopology B) :
      χ.app M ≫ P.map ((openImmersionLowerShriekToLowerStar B
          (pullback.fst e.g d.i)).app M) ≫
        (lowerStarComp B (pullback.fst e.g d.i) e.g (e.restrict.g ≫ d.i)
          e.isPullback_restrict.w).hom.app M =
      (openImmersionLowerShriekToLowerStar B d.i).app (R.obj M) ≫
        (lowerStarComp B e.restrict.g d.i).hom.app M := by
    exact ordinaryOpenExchange_inclusion A (pullback.fst e.g d.i)
      e.restrict.g e.g d.i e.isPullback_restrict M
  rw [towerSheafMap_eq A q v d e]
  have hm := raw_sheaf_tower A q v d e F G ah ae χ hχ M
  erw [hm]
  change ae.app _ ≫ (compactificationSheafToDirectImage A d).app _ ≫
    (lowerStar B v).map ((ah ≫ compactificationSheafToDirectImage A e.restrict).app M) ≫
      _ = _
  rw [nah, NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  change (etaleCompactificationGraphMap A v d).app (F.obj M) ≫
    (compactificationSheafToDirectImage A d).app (F.obj M) ≫
    (lowerStarComp B q v).hom.app M = _
  rw [reassoc_of% compactSupportGraphSheafComparison_normalization A v d (F.obj M)]

private noncomputable def rawDerivedTower
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {W V Y : Scheme.{u}}
    [IsNoetherian W] [IsNoetherian V] [IsNoetherian Y]
    (q : W ⟶ V) [IsProper q]
    (v : V ⟶ Y) [Etale v] [IsSeparated v] [QuasiCompact v]
    (d : Compactification v) (e : Compactification (q ≫ d.i)) :
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A) e.restrict.i).mapDerivedCategory ⋙
        (lowerStar (ModuleCat.{u + 1} A) e.restrict.g).rightDerivedFunctor) ⋙
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i).mapDerivedCategory ⋙
        (lowerStar (ModuleCat.{u + 1} A) d.g).rightDerivedFunctor) ⟶
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) e.i).mapDerivedCategory ⋙
        (lowerStar (ModuleCat.{u + 1} A) (e.g ≫ d.g)).rightDerivedFunctor := by
  let B := ModuleCat.{u + 1} A
  let J := openImmersionLowerShriek B e.restrict.i
  let O := openImmersionLowerShriek B (U := e.restrict.Z) (pullback.fst e.g d.i)
  let P := lowerStar B e.g
  let S := lowerStar B d.g
  let T := lowerStar B (e.g ≫ d.g)
  let eo := open_congr A e.restrict_i_fst.symm ≪≫
    openImmersionLowerShriekComp B e.restrict.i (pullback.fst e.g d.i)
  let ep := lowerStarComp B e.g d.g
  exact pasteDerivedTower
    (C := Sheaf W.smallEtaleTopology B)
    (U := Sheaf e.restrict.Z.smallEtaleTopology B)
    (Y := Sheaf V.smallEtaleTopology B)
    (X := Sheaf e.Z.smallEtaleTopology B)
    (Z := Sheaf d.Z.smallEtaleTopology B)
    (B := Sheaf Y.smallEtaleTopology B)
    J (lowerStar B e.restrict.g) (openImmersionLowerShriek B d.i)
    O P S (openImmersionLowerShriek B e.i) T
    (openImmersionLowerShriekLowerStarExchange B e.isPullback_restrict) eo ep

attribute [local irreducible] rawDerivedTower

private lemma rawDerivedTower_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {W V Y : Scheme.{u}}
    [IsNoetherian W] [IsNoetherian V] [IsNoetherian Y]
    (q : W ⟶ V) [IsProper q]
    (v : V ⟶ Y) [Etale v] [IsSeparated v] [QuasiCompact v]
    (d : Compactification v) (e : Compactification (q ≫ d.i)) :
    (rightDerivedLowerShriekOfCompactificationCompIso A d e).hom =
      rawDerivedTower A q v d e := by
  unfold rawDerivedTower pasteDerivedTower
  exact canonical_derived_tower A q v d e

section TowerProof

attribute [local instance 100000] Abelian.toPreadditive

set_option cleanup.letToHave false in
private theorem properEtaleCompositor_raw_unit_tower
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {W V Y : Scheme.{u}}
    [IsNoetherian W] [IsNoetherian V] [IsNoetherian Y]
    (q : W ⟶ V) [IsProper q]
    (v : V ⟶ Y) [Etale v] [IsSeparated v] [QuasiCompact v]
    [HasCompactification v] [HasCompactification (q ≫ v)]
    (d : Compactification v) (e : Compactification (q ≫ d.i))
    (K : HomotopyCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)) :
    let B := ModuleCat.{u + 1} A
    let J := openImmersionLowerShriek B e.restrict.i
    let R := lowerStar B e.restrict.g
    let I := openImmersionLowerShriek B d.i
    let _O := openImmersionLowerShriek B (U := e.restrict.Z) (pullback.fst e.g d.i)
    let _P := lowerStar B e.g
    let S := lowerStar B d.g
    let H := openImmersionLowerShriek B e.i
    let T := lowerStar B (e.g ≫ d.g)
    let F := lowerStar B q
    let G := etaleLowerShriek B v inferInstance
    let γh : F.rightDerivedFunctor ⟶ J.mapDerivedCategory ⋙ R.rightDerivedFunctor :=
      ((graphChosenProperComparison A q).symm ≪≫
        (rightDerivedLowerShriekIso A e.restrict).symm).hom
    let γe : G.mapDerivedCategory ⟶ I.mapDerivedCategory ⋙ S.rightDerivedFunctor :=
      (canonicalEtaleCompactSupportComparison A v d).inv
    let t : F ⋙ G ⟶ H ⋙ T := towerSheafMap A q v d e
    let D : (J.mapDerivedCategory ⋙ R.rightDerivedFunctor) ⋙
        (I.mapDerivedCategory ⋙ S.rightDerivedFunctor) ⟶
      H.mapDerivedCategory ⋙ T.rightDerivedFunctor := rawDerivedTower A q v d e
    G.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app K) ≫
      G.mapDerivedCategory.map (γh.app (DerivedCategory.Qh.obj K)) ≫
      γe.app ((J.mapDerivedCategory ⋙ R.rightDerivedFunctor).obj (DerivedCategory.Qh.obj K)) ≫
      D.app (DerivedCategory.Qh.obj K) =
      G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((t.mapHomotopyCategory (.up ℤ)).app K) ≫
        (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit H T).app K := by
  intro B J R I O P S H T F G γh γe t D
  let ah := properSupportInverse A q e.restrict
  have nah := properSupportInverse_normalization A q e.restrict
  let eo : H ≅ J ⋙ O := open_congr A e.restrict_i_fst.symm ≪≫
    openImmersionLowerShriekComp B e.restrict.i (pullback.fst e.g d.i)
  let ae := etaleCompactificationGraphMap A v d
  let χ : R ⋙ I ⟶ O ⋙ P := ordinaryOpenExchange A (U := e.restrict.Z)
    (pullback.fst e.g d.i) e.restrict.g e.g d.i e.isPullback_restrict
  let Γ := openImmersionLowerShriekLowerStarExchange B e.isPullback_restrict
  let ep := lowerStarComp B e.g d.g
  have hγh := fun L ↦ properCompactification_raw_unit A q e.restrict ah nah L
  have hγe := fun L ↦ graph_compactification_unit A v d L
  have hn (L : HomotopyCategory
      (Sheaf e.restrict.Z.smallEtaleTopology B) (.up ℤ)) :
      I.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app L) ≫
          Γ.app (DerivedCategory.Qh.obj L) ≫
          P.rightDerivedFunctor.map (O.mapDerivedCategoryFactorsh.hom.app L) =
        I.mapDerivedCategoryFactorsh.hom.app ((R.mapHomotopyCategory (.up ℤ)).obj L) ≫
          DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ I)) (.up ℤ)).hom.app L ≫
              (χ.mapHomotopyCategory (.up ℤ)).app L ≫
              (Functor.mapHomotopyCategoryCompIso (Iso.refl (O ⋙ P)) (.up ℤ)).inv.app L) ≫
          P.rightDerivedFunctorUnit.app ((O.mapHomotopyCategory (.up ℤ)).obj L) := by
    simpa only [χ, ordinaryOpenExchange_eq] using
      (openExchangeDerivedUnit A (U := e.restrict.Z)
        (pullback.fst e.g d.i) e.restrict.g e.g d.i e.isPullback_restrict L)
  have ht' : t = Functor.whiskerRight ah G ≫
      Functor.whiskerLeft J (Functor.whiskerLeft R ae) ≫
      Functor.whiskerLeft J (Functor.whiskerRight χ S) ≫
      Functor.whiskerLeft (J ⋙ O) ep.hom ≫ Functor.whiskerRight eo.inv T := by
    exact towerSheafMap_eq A q v d e
  have hd : D.app (DerivedCategory.Qh.obj K) =
      S.rightDerivedFunctor.map (Γ.app (J.mapDerivedCategory.obj (DerivedCategory.Qh.obj K))) ≫
        (Functor.rightDerivedFunctorCompIso' P S ep).hom.app
          ((J.mapDerivedCategory ⋙ O.mapDerivedCategory).obj (DerivedCategory.Qh.obj K)) ≫
        T.rightDerivedFunctor.map
          ((Functor.mapDerivedCategoryTriangleIso eo).inv.app (DerivedCategory.Qh.obj K)) := by
    dsimp only [D]
    unfold rawDerivedTower
    exact pasteDerivedTower_app J R I O P S H T Γ eo ep (DerivedCategory.Qh.obj K)
  have inferred := rightDerived_raw_unit_pasting_tower_app
    (dcC := (inferInstance : HasDerivedCategory.{u + 1} (Sheaf W.smallEtaleTopology B)))
    (dcU := (inferInstance : HasDerivedCategory.{u + 1} (Sheaf e.restrict.Z.smallEtaleTopology B)))
    (dcY := (inferInstance : HasDerivedCategory.{u + 1} (Sheaf V.smallEtaleTopology B)))
    (dcX := (inferInstance : HasDerivedCategory.{u + 1} (Sheaf e.Z.smallEtaleTopology B)))
    (dcZ := (inferInstance : HasDerivedCategory.{u + 1} (Sheaf d.Z.smallEtaleTopology B)))
    (dcB := (inferInstance : HasDerivedCategory.{u + 1} (Sheaf Y.smallEtaleTopology B)))
    J R I O P S H T F G ah ae γh γe hγh hγe χ Γ hn eo ep t ht' K D hd
  exact inferred

end TowerProof

private theorem properEtaleCompositor_raw_unit_core
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {W V Y : Scheme.{u}}
    [IsNoetherian W] [IsNoetherian V] [IsNoetherian Y]
    (q : W ⟶ V) [IsProper q]
    (v : V ⟶ Y) [Etale v] [IsSeparated v] [QuasiCompact v]
    [HasCompactification v] [HasCompactification (q ≫ v)]
    (c : Compactification (q ≫ v))
    (τ : lowerStar (ModuleCat.{u + 1} A) q ⋙
        etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g)
    (hτ : ∀ M, τ.app M ≫ (compactificationSheafToDirectImage A c).app M =
      etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) v
          ((lowerStar (ModuleCat.{u + 1} A) q).obj M) ≫
        (lowerStarComp (ModuleCat.{u + 1} A) q v).hom.app M)
    (e : Compactification (q ≫ (HasCompactification.compactification v).i))
    (K : HomotopyCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)) :
    (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory.map
        ((lowerStar (ModuleCat.{u + 1} A) q).rightDerivedFunctorUnit.app K) ≫
      (Functor.isoWhiskerRight (graphChosenProperComparison A q).symm
          (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory ≪≫
        Functor.isoWhiskerLeft (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q)
          (graphChosenEtaleComparison A v).symm ≪≫
        unboundedEtaleLowerShriekCompIso A q v ≪≫
        (rightDerivedLowerShriekIso A c).symm).hom.app (DerivedCategory.Qh.obj K) =
      (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategoryFactorsh.hom.app
          ((lowerStar (ModuleCat.{u + 1} A) q).mapHomotopyCategory (.up ℤ) |>.obj K) ≫
        DerivedCategory.Qh.map ((τ.mapHomotopyCategory (.up ℤ)).app K) ≫
        (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit
          (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i)
          (lowerStar (ModuleCat.{u + 1} A) c.g)).app K := by
  let B := ModuleCat.{u + 1} A
  let d := HasCompactification.compactification v
  let F := lowerStar B q
  let G := etaleLowerShriek B v inferInstance
  let t := towerSheafMap A q v d e
  have hu := properEtaleCompositor_raw_unit_tower A q v d e K
  have ht : t ≫ compactificationSheafToDirectImage A (d.comp e) =
      τ ≫ compactificationSheafToDirectImage A c := by
    apply NatTrans.ext
    funext M
    simp only [NatTrans.comp_app]
    exact (towerSheafMap_normalization A q v d e M).trans (hτ M).symm
  have hc := compactification_raw_unit_comparison A (q ≫ v) (F ⋙ G)
    (d.comp e) c t τ ht K
  have he := chosen_tower_comparison A q v e c
  dsimp only at he
  have hE := congrArg (fun z ↦
    G.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app K) ≫
      z.app (DerivedCategory.Qh.obj K)) he
  have h := congrArg (fun z ↦ z ≫
    (rightDerivedLowerShriekOfCompactificationIso A (d.comp e) c).hom.app
      (DerivedCategory.Qh.obj K)) hu
  have hc' := congrArg (fun z ↦
    G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫ z) hc
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc] at hE h hc'
  have hdapp := congrArg (fun z ↦ z.app (DerivedCategory.Qh.obj K))
    (rawDerivedTower_eq A q v d e)
  rw [hdapp] at hE
  exact hE.trans (h.trans hc')

/-- Proper-first compact-support composition carries the raw direct-image unit to the
mixed compactification unit after the degreewise normalized support map. This statement
has no graph transfer, base-change map, or adjunction transpose. -/
theorem properEtaleCompositor_raw_unit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {W V Y : Scheme.{u}}
    [IsNoetherian W] [IsNoetherian V] [IsNoetherian Y]
    (q : W ⟶ V) [IsProper q]
    (v : V ⟶ Y) [Etale v] [IsSeparated v] [QuasiCompact v]
    [HasCompactification v] [HasCompactification (q ≫ v)]
    (c : Compactification (q ≫ v))
    (τ : lowerStar (ModuleCat.{u + 1} A) q ⋙
        etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g)
    (hτ : ∀ M, τ.app M ≫ (compactificationSheafToDirectImage A c).app M =
      etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) v
          ((lowerStar (ModuleCat.{u + 1} A) q).obj M) ≫
        (lowerStarComp (ModuleCat.{u + 1} A) q v).hom.app M)
    (K : HomotopyCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)) :
    (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory.map
        ((lowerStar (ModuleCat.{u + 1} A) q).rightDerivedFunctorUnit.app K) ≫
      (Functor.isoWhiskerRight (graphChosenProperComparison A q).symm
          (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory ≪≫
        Functor.isoWhiskerLeft (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q)
          (graphChosenEtaleComparison A v).symm ≪≫
        unboundedEtaleLowerShriekCompIso A q v ≪≫
        (rightDerivedLowerShriekIso A c).symm).hom.app (DerivedCategory.Qh.obj K) =
      (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategoryFactorsh.hom.app
          ((lowerStar (ModuleCat.{u + 1} A) q).mapHomotopyCategory (.up ℤ) |>.obj K) ≫
        DerivedCategory.Qh.map ((τ.mapHomotopyCategory (.up ℤ)).app K) ≫
        (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit
          (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i)
          (lowerStar (ModuleCat.{u + 1} A) c.g)).app K := by
  exact properEtaleCompositor_raw_unit_core A q v c τ hτ
    ((HasCompactification.compactification (q ≫ v)).ofComp
      (HasCompactification.compactification v)) K

end AlgebraicGeometry.Etale
