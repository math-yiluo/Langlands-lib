/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Comma.Arrow
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassDiagonal
public import WeilConjectures.AlgebraicGeometry.Geo.GeoP1Cohomology
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerGeometryAdjunctionEvaluation
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleUnit
import WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheaf

/-! # Comparison of the normalized coefficient unit arrows

Source: blueprint latest, diagonal-tower trace proof, paragraph (1), the
identification of the coefficient-unit component before applying (G2).
(blueprint: lem-sfb-diagonal-trace-unit-arrow-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [local irreducible] Padic Padic.coefficientExtensionIntegers
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
  AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian in
section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

set_option backward.defeqAttrib.useBackward true in
private def unitsUnderEquivalences
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (b : L' ⊣ R') (F : C ≌ C') (G : D ≌ D')
    (α : F.functor ⋙ L' ≅ L ⋙ G.functor) (M : C) :
    Arrow.mk (F.functor.map (a.unit.app M)) ≅ Arrow.mk (b.unit.app (F.functor.obj M)) := by
  let β := conjugateIsoEquiv (a.comp G.toAdjunction) (F.toAdjunction.comp b) α
  let z := F.functor.mapIso
      (R.mapIso (G.unitIso.app (L.obj M)) ≪≫ β.app (G.functor.obj (L.obj M))) ≪≫
    F.counitIso.app (R'.obj (G.functor.obj (L.obj M))) ≪≫
    R'.mapIso (α.app M).symm
  refine Arrow.isoMk (Iso.refl _) z ?_
  simp only [Iso.refl_hom, Arrow.mk_hom, Category.id_comp]
  symm
  have h := unit_conjugateEquiv (a.comp G.toAdjunction) (F.toAdjunction.comp b) α.hom M
  have hh := congrArg (fun k ↦ F.functor.map k ≫
    (F.counitIso.app (R'.obj (G.functor.obj (L.obj M)))).hom ≫
      R'.map (α.inv.app M)) h
  simp only [Adjunction.comp_unit_app, Functor.comp_map, Functor.comp_obj,
    Functor.map_comp, Category.assoc] at hh
  simp only [Equivalence.toAdjunction_unit, Iso.app_hom, F.counit_naturality_assoc] at hh
  rw [← R'.map_comp, Iso.hom_inv_id_app] at hh
  simp only [Functor.comp_obj, Functor.id_obj, R'.map_id, Category.comp_id,
    F.functor_unit_comp_assoc] at hh
  simpa only [z, β, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom,
    Iso.app_inv, conjugateIsoEquiv_apply_hom, Functor.map_comp, Category.assoc,
    Equivalence.toAdjunction_unit] using hh

set_option backward.defeqAttrib.useBackward true in
private def unitArrowEvaluation
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (b : L' ⊣ R') (E₀ : C ⥤ C') (E₁ : D ⥤ D')
    (α : L ⋙ E₁ ≅ E₀ ⋙ L') (β : R ⋙ E₀ ≅ E₁ ⋙ R')
    (hu : ∀ M, E₀.map (a.unit.app M) ≫ β.hom.app (L.obj M) ≫
      R'.map (α.hom.app M) = b.unit.app (E₀.obj M))
    (M : C) {N : D} (u : L.obj M ≅ N) {P : C'} (j : P ≅ E₀.obj M) :
    Arrow.mk (b.unit.app P) ≅ Arrow.mk (E₀.map (a.unit.app M ≫ R.map u.hom)) := by
  let d := (α.app M).symm ≪≫ E₁.mapIso u
  let z := R'.mapIso (L'.mapIso j ≪≫ d) ≪≫ (β.app N).symm
  have h : E₀.map (a.unit.app M ≫ R.map u.hom) ≫ β.hom.app N =
      b.unit.app (E₀.obj M) ≫ R'.map d.hom := by
    calc
      _ = E₀.map (a.unit.app M) ≫ β.hom.app (L.obj M) ≫
          R'.map (E₁.map u.hom) := by
        simpa only [Functor.map_comp, Functor.comp_map, Category.assoc] using
          congrArg (fun k ↦ E₀.map (a.unit.app M) ≫ k) (β.hom.naturality u.hom)
      _ = _ := by
        rw [← hu M]
        simp only [d, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom,
          Functor.map_comp, Category.assoc]
        have hc : R'.map (α.hom.app M) ≫ R'.map (α.inv.app M) = 𝟙 _ := by
          rw [← R'.map_comp, Iso.hom_inv_id_app, R'.map_id]
        simpa only [Functor.comp_obj, Category.assoc, Category.id_comp] using
          (congrArg (fun k ↦ E₀.map (a.unit.app M) ≫ β.hom.app (L.obj M) ≫
            k ≫ R'.map (E₁.map u.hom)) hc).symm
  have hz : z.hom ≫ β.hom.app N = R'.map (L'.map j.hom ≫ d.hom) := by
    simp only [z, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv,
      Functor.comp_obj]
    rw [Category.assoc, Iso.inv_hom_id_app]
    simpa only [Functor.comp_obj] using Category.comp_id (R'.map (L'.map j.hom ≫ d.hom))
  refine Arrow.isoMk j z ?_
  apply (cancel_mono (β.hom.app N)).mp
  change (j.hom ≫ E₀.map (a.unit.app M ≫ R.map u.hom)) ≫ β.hom.app N =
    (b.unit.app P ≫ z.hom) ≫ β.hom.app N
  simp only [Category.assoc]
  rw [h, hz]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun k ↦ k ≫ R'.map d.hom) (b.unit_naturality j.hom).symm

private def nativePullRealization (A : Type u) [CommRing A] [Finite A]
    {X S : Scheme.{u}} (f : X ⟶ S) :
    (Scheme.sfIntrinsicModuleEquivalence S A).functor.mapDerivedCategory ⋙
        Scheme.proEtaleConstantRingDerivedPullback A f ≅
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).mapDerivedCategory ⋙
        (Scheme.sfIntrinsicModuleEquivalence X A).functor.mapDerivedCategory := by
  have hr : Scheme.proEtaleRingDirectImageMap f (Scheme.proEtaleConstantRing S A)
      (Scheme.proEtaleConstantRing X A) (Scheme.proEtaleConstantRingComparison f A) =
        Scheme.proEtaleCoefficientDirectImageMap f A :=
    ((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
  let r : Scheme.proEtaleConstantRingPushforward A f ≅
      Scheme.proEtaleConstantModuleDirectImage f A :=
    SheafOfModules.pushforwardCongr (by rw [hr])
  let d := ((Scheme.proEtaleConstantRingAdjunction A f).ofNatIsoRight r).leftAdjointUniq
    (Scheme.sfIntrinsicConstantModuleAdjunction f A)
  let e := Scheme.sfIntrinsicModuleEquivalence S A
  let H := upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  let K := (Scheme.sfIntrinsicModuleEquivalence X A).functor
  exact Functor.isoWhiskerLeft e.functor.mapDerivedCategory
      (Functor.mapDerivedCategoryNatIso d) ≪≫
    Functor.mapDerivedCategoryCompIso e.functor (Scheme.sfIntrinsicPullback A f) ≪≫
    Functor.mapDerivedCategoryNatIso (e.funInvIdAssoc (H ⋙ K)) ≪≫
    (Functor.mapDerivedCategoryCompIso H K).symm

private def linePullRealization (A : Type u) [CommRing A] [Finite A]
    {X S : Scheme.{u}} {f : X ⟶ S} (e : X ≅ ProjectiveLine S)
    (he : e.hom ≫ (ProjectiveLine S ↘ S) = f) :
    (Scheme.sfIntrinsicModuleEquivalence S A).functor.mapDerivedCategory ⋙
        Scheme.proEtaleConstantRingDerivedPullback A f ≅
      geoP1Pullback (ULift.{u + 1} A) (ProjectiveLine S ↘ S) ⋙
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) e.hom).mapDerivedCategory ⋙
          (Scheme.sfIntrinsicModuleEquivalence X A).functor.mapDerivedCategory) := by
  let C := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let p := ProjectiveLine S ↘ S
  let H := (upperStar C e.hom).mapDerivedCategory
  let K := (Scheme.sfIntrinsicModuleEquivalence X A).functor.mapDerivedCategory
  let t : upperStar C f ≅ upperStar C p ⋙ upperStar C e.hom :=
    eqToIso (congrArg (fun h : X ⟶ S ↦ upperStar C h) he.symm) ≪≫
      upperStarComp C e.hom p
  exact nativePullRealization A f ≪≫
    Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryNatIso t ≪≫
        (Functor.mapDerivedCategoryCompIso (upperStar C p) (upperStar C e.hom)).symm) K ≪≫
    Functor.associator (upperStar C p).mapDerivedCategory H K ≪≫
    Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory C p).symm (H ⋙ K)

private theorem compare_adjunct
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (F : C ⥤ C') (G : D ⥤ D') (a : L ⊣ R) (b : L' ⊣ R')
    (α : F ⋙ L' ≅ L ⋙ G) {M : C} {N : D} (h : L.obj M ⟶ N) :
    F.map (a.homEquiv _ _ h) ≫ b.homEquiv _ _
        (α.hom.app (R.obj N) ≫ G.map (a.counit.app N)) =
      b.homEquiv _ _ (α.hom.app M ≫ G.map h) := by
  rw [← b.homEquiv_naturality_left]
  congr 1
  rw [← Category.assoc, ← Functor.comp_map, α.hom.naturality]
  simp only [Functor.comp_map, Category.assoc, ← G.map_comp]
  congr 1
  change G.map ((a.homEquiv M N).symm ((a.homEquiv M N) h)) = G.map h
  rw [Equiv.symm_apply_apply]

private def comparedUnitArrow (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    Arrow.mk ((geoP1Comparison A S).map (Etale.p1DecompositionUnit A S) ≫
      geoP1PushComparison A (ProjectiveLine S ↘ S)
        (Etale.ordinaryFiniteUnit A (ProjectiveLine S))) ≅
      Arrow.mk ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
        (ProjectiveLine S ↘ S)).unit.app (geoP1Unit A S)) := by
  let p := ProjectiveLine S ↘ S
  refine Iso.symm ?_
  refine Arrow.isoMk (Iso.refl _)
    ((geoP1Pushforward A p).mapIso (geoP1UnitPullback A p)) ?_
  simp only [Iso.refl_hom, Category.id_comp, Arrow.mk_hom, Functor.mapIso_hom]
  have h := compare_adjunct (geoP1Comparison A S) (geoP1Comparison A (ProjectiveLine S))
    (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
    (geoP1PullComparison A p) (Etale.ordinaryFiniteUnitPullback A p).hom
  simpa only [Etale.p1DecompositionUnit, geoP1PushComparison, geoP1UnitPullback,
    geoP1Unit, geoP1Pushforward, Etale.ordinaryFinitePushforward, p, Functor.id_obj,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Adjunction.homEquiv_unit] using h

private def geoCoefficientIso (A : Type u) [CommRing A] [Finite A] (T : Scheme.{u}) :
    (Scheme.sfIntrinsicModuleEquivalence T A).functor.mapDerivedCategory.obj
        (geoP1Unit (ULift.{u + 1} A) T) ≅
      (DerivedCategory.singleFunctor _ 0).obj (Scheme.proEtaleConstantModule T A) := by
  let F := (Scheme.sfIntrinsicModuleEquivalence T A).functor
  let C := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let M := ModuleCat.of (ULift.{u + 1} A) (ULift.{u + 1} A)
  exact F.mapDerivedCategory.mapIso
      (((comparisonUpperStar C T).mapDerivedCategorySingleFunctor 0).app
          (Etale.ordinaryFiniteConstant (ULift.{u + 1} A) T) ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso
          ((constantSheafCompComparisonUpperStarIso C T).app M)) ≪≫
    (F.mapDerivedCategorySingleFunctor 0).app (Scheme.proEtaleFixedConstantModule T A) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (Scheme.proEtaleConstantModuleUnit T A)

private def unitSourceIso {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) {M N : C} (e : M ≅ N) :
    Arrow.mk (a.unit.app M) ≅ Arrow.mk (a.unit.app N) :=
  Arrow.isoMk e (R.mapIso (L.mapIso e)) (a.unit.naturality e.hom)

private def coefficientEvaluationMap
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) (n : ℕ) :
    Scheme.proEtaleConstantModule T (SpTowerShriek.R l E n) ⟶
      (SpTowerShriek.ev l E T n).obj (coefficient T (Arings l E T)) :=
  SheafOfModules.unitToPushforwardObjUnit
    (eqToHom (WeilConjectures.SemilinearSections.evaluation_ring
      (Scheme.ProEt.topology T) (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) n).symm)

private theorem coefficientEvaluationMap_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) (n : ℕ) : IsIso (coefficientEvaluationMap l E T n) := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf _)]
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _)]
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  rw [← isIso_iff_of_reflects_iso _ (forget AddCommGrpCat)]
  change IsIso ((forget RingCat).map
    ((eqToHom (WeilConjectures.SemilinearSections.evaluation_ring
      (Scheme.ProEt.topology T) (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T)
        n).symm).hom.app U))
  infer_instance

private def coefficientEvaluationIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) (n : ℕ) :
    (DerivedCategory.singleFunctor _ 0).obj
        (Scheme.proEtaleConstantModule T (SpTowerShriek.R l E n)) ≅
      (SpTowerShriek.Ev l E T n).obj (unit T (Arings l E T)) := by
  letI := coefficientEvaluationMap_isIso l E T n
  exact (DerivedCategory.singleFunctor _ 0).mapIso
      (asIso (coefficientEvaluationMap l E T n)) ≪≫
    (((SpTowerShriek.ev l E T n).mapDerivedCategorySingleFunctor 0).app
      (coefficient T (Arings l E T))).symm

private def evaluatedUnitArrowIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X S : Scheme.{u}} (b : SpTowerShriek.Base l E) {f : X ⟶ S}
    (g : SpTowerShriek.Geometry l E b f) (c : CoefficientPullback l E b f g)
    (n : ℕ) :
    Arrow.mk ((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n)
        f).mapDerivedCategoryRightDerivedAdjunction.unit.app
        ((DerivedCategory.singleFunctor _ 0).obj
          (Scheme.proEtaleConstantModule S (SpTowerShriek.R l E n)))) ≅
      Arrow.mk ((SpTowerShriek.Ev l E S n).map (unitArrow l E c)) := by
  exact unitArrowEvaluation (SpTowerShriek.adjunction l E b g)
    (Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n)
      f).mapDerivedCategoryRightDerivedAdjunction
    (SpTowerShriek.Ev l E S n) (SpTowerShriek.Ev l E X n)
    (g.pullEvaluation n) (g.pushEvaluation n)
    (SpTowerShriek.geometry_adjunction_evaluation l E b g n).1
    (unit S (Arings l E S)) (c.derivedIso l E) (coefficientEvaluationIso l E S n)

/-- Evaluation and coefficient realization identify the actual coefficient unit
with the image of the ordinary etale coefficient unit, as an arrow.

Source: `sk-prop-diagonal-tower-trace.proof.md` (1), identification with the
finite coefficient map, before applying projective-line cohomology (G2).
(blueprint: lem-sfb-diagonal-trace-unit-arrow-comparison).

Proof: the etale/pro-etale direct-image comparison is defined as the mate of
its inverse-image comparison. Expanding this mate identifies the compared etale
unit with the pro-etale adjunction unit followed by pushforward of the specified
constant-object pullback isomorphism. In particular this argument does not need
the direct-image comparison to be invertible.

For the realization step, the intrinsic tensor direct image and the realized
fixed-scalar direct image have the same coefficient map. Uniqueness of their
left adjoints identifies the two ordinary pullbacks. Descend this isomorphism
by exact functors, and compose with the pullback compositor for e over S.
Pullback along e and coefficient realization are equivalences. Conjugating
the two adjunctions through these equivalences identifies their unit arrows:
the conjugate of the invertible pullback comparison is invertible, and its
unit equation gives the commuting square.

Comparison of constant sheaves and the canonical constant-module realization
identify the source with the regular intrinsic module in degree zero. The
ring equality defining level evaluation identifies this regular module with
the evaluated tower coefficient object. Finally, the unit identity in
geometry_adjunction_evaluation and naturality of pushEvaluation give the
remaining square. The target isomorphism includes the inverse pullEvaluation
and the image of c.derivedIso. Its invertibility suffices: no separately fixed
endpoint comparison is asserted, so c.normalization need not be invoked.
All constructions apply to the empty scheme and the zero coefficient ring;
no Chern class or projective-line decomposition is used. -/
theorem diagonalTrace_unit_arrow_comparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    (b : SpTowerShriek.Base l E) {f : X ⟶ S}
    (e : X ≅ ProjectiveLine S) (he : e.hom ≫ (ProjectiveLine S ↘ S) = f)
    (g : SpTowerShriek.Geometry l E b f) (c : CoefficientPullback l E b f g)
    (n : ℕ) [Finite (SpTowerShriek.R l E n)] :
    let A := ULift.{u + 1} (SpTowerShriek.R l E n)
    let F := (Scheme.sfIntrinsicModuleEquivalence S
      (SpTowerShriek.R l E n)).functor.mapDerivedCategory
    Nonempty (Arrow.mk
      (F.map ((geoP1Comparison A S).map (Etale.p1DecompositionUnit A S) ≫
        geoP1PushComparison A (ProjectiveLine S ↘ S)
          (Etale.ordinaryFiniteUnit A (ProjectiveLine S)))) ≅
      Arrow.mk ((SpTowerShriek.Ev l E S n).map (unitArrow l E c))) := by
  let A := SpTowerShriek.R l E n
  let F := Scheme.sfIntrinsicDerivedEquivalence S A
  let H := (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) e.hom).mapDerivedCategory
  let G := (H ⋙ (Scheme.sfIntrinsicDerivedEquivalence X A).functor).asEquivalence
  let a := derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) (ProjectiveLine S ↘ S)
  let d := (Scheme.proEtaleConstantRingAdjunction A f).mapDerivedCategoryRightDerivedAdjunction
  exact ⟨F.functor.mapArrow.mapIso (comparedUnitArrow (ULift.{u + 1} A) S) ≪≫
    unitsUnderEquivalences a d F G (linePullRealization A e he) _ ≪≫
    unitSourceIso d (geoCoefficientIso A S) ≪≫ evaluatedUnitArrowIso l E b g c n⟩

end AlgebraicGeometry.ProEtale.DiagonalTrace

end
