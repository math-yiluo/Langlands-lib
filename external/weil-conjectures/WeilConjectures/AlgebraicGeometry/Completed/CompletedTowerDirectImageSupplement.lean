/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerDerivedLimitFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.AlgebraicGeometry.Completed.CompletedScalarProjectionPerfectIso
import WeilConjectures.CategoryTheory.Right.RightDerivedComplexUnitNormalization
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import WeilConjectures.AlgebraicGeometry.CompletedTowerDirectImage

/-!
# Total direct image of strict completed-coefficient towers

Source: blueprint sec-proper-base-change/sk-thm-properbasechange, order 1276;
Stacks Project, Tag 099N (blueprint: proposition-proper-base-change-complete-integral--1).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite

private theorem inverse_square_iff {C : Type*} [Category* C]
    {A B D E F G : C} (e : B ≅ D) (p : A ≅ F) (k : F ≅ G) (q : D ≅ E)
    (a : A ⟶ B) (b : G ⟶ E) :
    b ≫ q.inv ≫ e.inv = k.inv ≫ p.inv ≫ a ↔
      a ≫ e.hom ≫ q.hom = p.hom ≫ k.hom ≫ b := by
  constructor
  · intro h
    have hh := congrArg (fun z ↦ p.hom ≫ k.hom ≫ z ≫ e.hom ≫ q.hom) h
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id] using hh.symm
  · intro h
    have hh := congrArg (fun z ↦ k.inv ≫ p.inv ≫ z ≫ q.inv ≫ e.inv) h
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
      Iso.hom_inv_id, Category.comp_id] using hh.symm

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
  (d : AdicCoefficientDatum A)

/-- Sectionwise module direct image with the completed coefficient action.
Source: blueprint order 1276 (blueprint: proposition-proper-base-change-complete-integral--1). -/
def completedModuleDirectImage :
    pbcModules X (pbcAdicCompletion X d) ⥤ pbcModules Y (pbcAdicCompletion Y d) :=
  SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
    (J := ProEt.topology Y) (K := ProEt.topology X)
    (S := reductionModuleRing Y (pbcAdicCompletion Y d))
    (R := reductionModuleRing X (pbcAdicCompletion X d))
    ⟨Functor.whiskerRight (completedCoefficientDirectImageMap f d).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

/-- Sectionwise completed direct image is additive.
Source: blueprint order 1276 (blueprint: proposition-proper-base-change-complete-integral--1).
Proof: direct image applies the same underlying maps to sections on base-changed objects.
Addition of linear maps is sectionwise, so direct image preserves addition. -/
@[instance]
theorem completedModuleDirectImage_additive : (completedModuleDirectImage f d).Additive := by
  constructor
  intro M N g h
  rfl

/-- The unbounded total derived completed-coefficient module direct image.
Source: blueprint order 1276 (blueprint: proposition-proper-base-change-complete-integral--1). -/
abbrev completedDerivedDirectImage :
    DerivedCategory (pbcModules X (pbcAdicCompletion X d)) ⥤
      DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)) :=
  (completedModuleDirectImage f d).rightDerivedFunctor

private theorem completedCoefficient_isIso :
    IsIso (completedCoefficientMap f d) := by
  let Q : ℕᵒᵖ ⥤ CommRingCat.{u + 1} := Functor.ofOpSequence
    (X := fun n ↦ CommRingCat.of (A ⧸ d.ideal ^ (n + 1)))
    (fun n ↦ CommRingCat.ofHom (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
  let : ∀ n : ℕᵒᵖ, Finite (Q.obj n) := fun n ↦ d.quotientFinite n.unop
  let e (W : Scheme.{u}) : proEtaleCoefficientTower W Q ≅ adicLisseRingSystem W d.ideal :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _)
      (fun f ↦ (NatTrans.ofOpSequence
        (F := proEtaleCoefficientTower W Q) (G := adicLisseRingSystem W d.ideal)
        (fun _ ↦ 𝟙 _) (fun n ↦ by
          simp [proEtaleCoefficientTower, Q, adicLisseRingSystem])).naturality f)
  let b (W : Scheme.{u}) := e W ≪≫ pbcConstantSystemComparison W d
  let c (W : Scheme.{u}) := HasLimit.isoOfNatIso (b W)
  let L := proEtaleSheafInverseImage f CommRingCat.{u + 1}
  let := (proEtale_profinite_coefficient_inverse_image Q).2.1 X Y f
  let t := L.mapIso (c Y).symm ≪≫ asIso (proEtaleProfiniteComparison f Q) ≪≫ c X
  suffices h : completedCoefficientMap f d = t.hom by
    rw [h]
    infer_instance
  apply limit.hom_ext
  rintro ⟨n⟩
  dsimp only [completedCoefficientMap, t, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  simp only [limit.lift_π, Category.assoc]
  dsimp only [c]
  rw [HasLimit.isoOfNatIso_hom_π]
  simp only [asIso_hom]
  rw [reassoc_of% (proEtale_profinite_coefficient_inverse_image Q).2.2.1 X Y f (op n)]
  rw [← Category.assoc, ← Category.assoc, ← L.map_comp]
  rw [HasLimit.isoOfNatIso_inv_π]
  simp only [L.map_comp, Category.assoc]
  dsimp only [b, e, Iso.trans_hom, NatIso.ofComponents_hom_app, Iso.refl_hom,
    Category.id_comp, proEtaleConstantComparison]
  simp only [completedCoefficientComponent, completedFiniteCoefficientMap, Category.assoc,
    L, pbcConstantSystemComparison, pbcAdicProjection, Q, Iso.trans_inv,
    NatTrans.comp_app, NatIso.ofComponents_inv_app, NatIso.ofComponents_hom_app,
    Iso.refl_inv, Functor.map_comp]
  dsimp only [proEtaleCoefficientTower, Functor.comp_obj, Functor.ofOpSequence_obj]
  simp only [Iso.refl_hom, Category.id_comp]
  change L.map (pbcAdicProjection Y d n) ≫
      L.map (pbcLevelConstantComparison Y d n).inv ≫
      proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
        (CommRingCat.of (A ⧸ d.ideal ^ (n + 1))) ≫
      (pbcLevelConstantComparison X d n).hom =
    L.map (pbcAdicProjection Y d n) ≫
      L.map (pbcLevelConstantComparison Y d n).inv ≫
      L.map (𝟙 (adicLisseConstantRing Y
        (A ⧸ d.ideal ^ (n + 1)))) ≫
      proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
        (CommRingCat.of (A ⧸ d.ideal ^ (n + 1))) ≫
      (pbcLevelConstantComparison X d n).hom
  rw [L.map_id, Category.id_comp]

/-- Module direct image with the actual finite quotient coefficient ring.
Source: blueprint order 1276 (blueprint: proposition-proper-base-change-complete-integral--1). -/
abbrev completedFiniteModuleDirectImage (n : ℕ) :=
  proEtaleRingModuleDirectImage f ((pbcAdicRings Y d).obj (op n))
    ((pbcAdicRings X d).obj (op n))
    (asIso (completedFiniteCoefficientMap f d n))

/-- The finite quotient direct image obtained by total right derivation.
Source: blueprint order 1276 (blueprint: proposition-proper-base-change-complete-integral--1). -/
abbrev completedFiniteDerivedDirectImage (n : ℕ) :=
  (completedFiniteModuleDirectImage f d n).rightDerivedFunctor

private theorem completedCoefficient_projection (n : ℕ) :
    completedCoefficientMap f d ≫ pbcAdicProjection X d n =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (pbcAdicProjection Y d n) ≫
        completedFiniteCoefficientMap f d n := by
  exact limit.lift_π _ (op n)

/-- Restriction commutes with ordinary direct image by identity on underlying sections.
Source: blueprint order 1276 (blueprint: proposition-proper-base-change-complete-integral--1).
Proof: the square of completed structure maps and finite projections commutes by the
component construction of c_f. The two module actions therefore agree. Identity on
sections is a natural linear isomorphism and sectionwise faithfulness proves uniqueness. -/
theorem completedRestrictionDirectImageIso_exists (n : ℕ) :
    ∃! e : pbcRestrict (pbcAdicProjection X d n) ⋙ completedModuleDirectImage f d ≅
        completedFiniteModuleDirectImage f d n ⋙ pbcRestrict (pbcAdicProjection Y d n),
      ∀ (M : pbcModules X ((pbcAdicRings X d).obj (op n))) (U : Y.ProEtᵒᵖ)
        (x : ((pbcRestrict (pbcAdicProjection X d n) ⋙
          completedModuleDirectImage f d).obj M).val.obj U),
        (e.hom.app M).val.app U x = x := by
  let := completedCoefficient_isIso f d
  obtain ⟨e, he, _⟩ := proEtaleRingRestrictionDirectImage_existsUnique f
    (pbcAdicCompletion Y d) ((pbcAdicRings Y d).obj (op n))
    (pbcAdicCompletion X d) ((pbcAdicRings X d).obj (op n))
    (pbcAdicProjection Y d n) (pbcAdicProjection X d n)
    (asIso (completedCoefficientMap f d)) (asIso (completedFiniteCoefficientMap f d n))
    (completedCoefficient_projection f d n)
  refine ⟨e.symm, ?_, ?_⟩
  · intro M U x
    have h := he M U ((e.inv.app M).val.app U x)
    have hi := congrArg (fun t ↦ t.val.app U x) (e.inv_hom_id_app M)
    change (e.hom.app M).val.app U ((e.inv.app M).val.app U x) = x at hi
    exact h.symm.trans hi
  · intro e' he'
    apply Iso.ext
    ext M U x
    exact (he' M U x).trans (by
      have h := he M U ((e.inv.app M).val.app U x)
      have hi := congrArg (fun t ↦ t.val.app U x) (e.inv_hom_id_app M)
      change (e.hom.app M).val.app U ((e.inv.app M).val.app U x) = x at hi
      exact (h.symm.trans hi).symm)

/-- The uniquely section-normalized restriction/direct-image comparison.
Source: blueprint order 1276 (blueprint: proposition-proper-base-change-complete-integral--1). -/
def completedRestrictionDirectImageIso (n : ℕ) :
    pbcRestrict (pbcAdicProjection X d n) ⋙ completedModuleDirectImage f d ≅
      completedFiniteModuleDirectImage f d n ⋙ pbcRestrict (pbcAdicProjection Y d n) :=
  (completedRestrictionDirectImageIso_exists f d n).exists.choose

/-- The total right-derived comparison on a completed-coefficient cochain complex.
Source: blueprint order 1276 (blueprint: proposition-proper-base-change-complete-integral--1). -/
def completedDirectImageComplexUnit
    (C : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ) :
    DerivedCategory.Q.obj
        (((completedModuleDirectImage f d).mapHomologicalComplex (.up ℤ)).obj C) ⟶
      (completedDerivedDirectImage f d).obj (DerivedCategory.Q.obj C) :=
  (DerivedCategory.quotientCompQhIso _).inv.app _ ≫
    DerivedCategory.Qh.map
      (((completedModuleDirectImage f d).mapHomotopyCategoryFactors (.up ℤ)).inv.app C) ≫
    (completedModuleDirectImage f d).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj C) ≫
    (completedDerivedDirectImage f d).map ((DerivedCategory.quotientCompQhIso _).hom.app C)

/-- The total right-derived comparison on a finite-coefficient cochain complex.
Source: blueprint order 1276 (blueprint: proposition-proper-base-change-complete-integral--1). -/
def completedFiniteDirectImageComplexUnit (n : ℕ)
    (C : CochainComplex (pbcModules X ((pbcAdicRings X d).obj (op n))) ℤ) :
    DerivedCategory.Q.obj
        (((completedFiniteModuleDirectImage f d n).mapHomologicalComplex (.up ℤ)).obj C) ⟶
      (completedFiniteDerivedDirectImage f d n).obj (DerivedCategory.Q.obj C) :=
  (DerivedCategory.quotientCompQhIso _).inv.app _ ≫
    DerivedCategory.Qh.map
      (((completedFiniteModuleDirectImage f d n).mapHomotopyCategoryFactors (.up ℤ)).inv.app C) ≫
    (completedFiniteModuleDirectImage f d n).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj C) ≫
    (completedFiniteDerivedDirectImage f d n).map
      ((DerivedCategory.quotientCompQhIso _).hom.app C)

-- Compare the explicit scalar-restriction implementations of the same functors.
set_option Elab.async false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The derived coefficient comparison is fixed by the ordinary identity comparison
and the universal right-derived units. This normalization prevents an arbitrary
natural isomorphism from being substituted in the projection-formula construction.
Source: blueprint order 1276 (blueprint: proposition-proper-base-change-complete-integral--1).
Proof: finite module inverse image is exact, and direct images of injective finite
module sheaves are acyclic after scalar restriction. Derive the sectionwise comparison
using such resolutions. The universal right-derived units give the displayed equation
on complexes, and the universal derived property gives uniqueness and invertibility. -/
theorem completedDerivedRestrictionDirectImageIso_exists (n : ℕ) :
    ∃! e : pbcDerivedRestrict (pbcAdicProjection X d n) ⋙ completedDerivedDirectImage f d ≅
        completedFiniteDerivedDirectImage f d n ⋙
          pbcDerivedRestrict (pbcAdicProjection Y d n),
      ∀ C : CochainComplex (pbcModules X ((pbcAdicRings X d).obj (op n))) ℤ,
        completedDirectImageComplexUnit f d
            (((pbcRestrict (pbcAdicProjection X d n)).mapHomologicalComplex (.up ℤ)).obj C) ≫
          (completedDerivedDirectImage f d).map
            ((pbcRestrict (pbcAdicProjection X d n)).mapDerivedCategoryFactors.inv.app C) ≫
          e.hom.app (DerivedCategory.Q.obj C) =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (completedRestrictionDirectImageIso f d n).hom (.up ℤ)).app C) ≫
          (pbcRestrict (pbcAdicProjection Y d n)).mapDerivedCategoryFactors.inv.app
            (((completedFiniteModuleDirectImage f d n).mapHomologicalComplex (.up ℤ)).obj C) ≫
          (pbcDerivedRestrict (pbcAdicProjection Y d n)).map
            (completedFiniteDirectImageComplexUnit f d n C) := by
  let := completedCoefficient_isIso f d
  let RX := pbcRestrict (pbcAdicProjection X d n)
  let RY := pbcRestrict (pbcAdicProjection Y d n)
  let F := completedModuleDirectImage f d
  let G := completedFiniteModuleDirectImage f d n
  let comm := completedCoefficient_projection f d n
  let cR := asIso (completedCoefficientMap f d)
  let cS := asIso (completedFiniteCoefficientMap f d n)
  let i := proEtaleRingRestrictionDirectImage f
    (pbcAdicCompletion Y d) ((pbcAdicRings Y d).obj (op n))
    (pbcAdicCompletion X d) ((pbcAdicRings X d).obj (op n))
    (pbcAdicProjection Y d n) (pbcAdicProjection X d n) cR cS comm
  have hi : i = (completedRestrictionDirectImageIso f d n).symm := by
    suffices h : i.symm = completedRestrictionDirectImageIso f d n from
      congrArg Iso.symm h
    apply (completedRestrictionDirectImageIso_exists f d n).unique
    · intro M U x
      have he := (Classical.choose_spec
        (proEtaleRingRestrictionDirectImage_existsUnique f
          (pbcAdicCompletion Y d) ((pbcAdicRings Y d).obj (op n))
          (pbcAdicCompletion X d) ((pbcAdicRings X d).obj (op n))
          (pbcAdicProjection Y d n) (pbcAdicProjection X d n) cR cS comm)).1
      have h := he M U ((i.inv.app M).val.app U x)
      have h' := congrArg (fun t ↦ t.val.app U x) (i.inv_hom_id_app M)
      change (i.hom.app M).val.app U ((i.inv.app M).val.app U x) = x at h'
      exact h.symm.trans h'
    · exact (completedRestrictionDirectImageIso_exists f d n).exists.choose_spec
  obtain ⟨e, he, hue⟩ := proEtaleRingRestrictionDerivedDirectImage_existsUnique f
    (pbcAdicCompletion Y d) ((pbcAdicRings Y d).obj (op n))
    (pbcAdicCompletion X d) ((pbcAdicRings X d).obj (op n))
    (pbcAdicProjection Y d n) (pbcAdicProjection X d n) cR cS comm
  have hn (e' : G.rightDerivedFunctor ⋙ RY.mapDerivedCategory ≅
      RX.mapDerivedCategory ⋙ F.rightDerivedFunctor)
      (C : CochainComplex (pbcModules X ((pbcAdicRings X d).obj (op n))) ℤ) :=
    inverse_square_iff (e'.app (DerivedCategory.Q.obj C))
      (RY.mapDerivedCategoryFactors.app ((G.mapHomologicalComplex (.up ℤ)).obj C))
      (DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex
        (completedRestrictionDirectImageIso f d n).symm (.up ℤ)).app C))
      (F.rightDerivedFunctor.mapIso (RX.mapDerivedCategoryFactors.app C))
      (RY.mapDerivedCategory.map (completedFiniteDirectImageComplexUnit f d n C))
      (completedDirectImageComplexUnit f d
        ((RX.mapHomologicalComplex (.up ℤ)).obj C))
  have uF (C : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ) :
      completedDirectImageComplexUnit f d C =
        proEtaleRingDirectImageDerivedUnit f _ _ cR C := by
    have hid : ((completedModuleDirectImage f d).mapHomotopyCategoryFactors
        (.up ℤ)).inv.app C = 𝟙 _ := rfl
    dsimp only [completedDirectImageComplexUnit, proEtaleRingDirectImageDerivedUnit]
    rw [hid]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  have uG (C : CochainComplex (pbcModules X ((pbcAdicRings X d).obj (op n))) ℤ) :
      completedFiniteDirectImageComplexUnit f d n C =
        proEtaleRingDirectImageDerivedUnit f _ _ cS C := by
    have hid : ((completedFiniteModuleDirectImage f d n).mapHomotopyCategoryFactors
        (.up ℤ)).inv.app C = 𝟙 _ := rfl
    dsimp only [completedFiniteDirectImageComplexUnit, proEtaleRingDirectImageDerivedUnit]
    rw [hid]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
  refine ⟨e.symm, ?_, ?_⟩
  · intro C
    apply (hn e C).2
    have heC := he C
    change RY.mapDerivedCategory.map
        (proEtaleRingDirectImageDerivedUnit f _ _ cS C) ≫
        e.hom.app (DerivedCategory.Q.obj C) ≫
        F.rightDerivedFunctor.map (RX.mapDerivedCategoryFactors.hom.app C) =
      RY.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj C) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex i (.up ℤ)).hom.app C) ≫
        proEtaleRingDirectImageDerivedUnit f _ _ cR
          ((RX.mapHomologicalComplex (.up ℤ)).obj C) at heC
    simpa only [hi, uF, uG, Functor.mapIso_hom, Iso.app_hom] using heC
  · intro e' he'
    have hh : e'.symm = e := hue e'.symm (by
      intro C
      have h := (hn e'.symm C).1 (he' C)
      change RY.mapDerivedCategory.map
          (proEtaleRingDirectImageDerivedUnit f _ _ cS C) ≫
          e'.symm.hom.app (DerivedCategory.Q.obj C) ≫
          F.rightDerivedFunctor.map (RX.mapDerivedCategoryFactors.hom.app C) =
        RY.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj C) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex i (.up ℤ)).hom.app C) ≫
          proEtaleRingDirectImageDerivedUnit f _ _ cR
            ((RX.mapHomologicalComplex (.up ℤ)).obj C)
      simpa only [hi, uF, uG, Functor.mapIso_hom, Iso.app_hom] using h)
    exact congrArg Iso.symm hh

/-- The canonical derived restriction/direct-image comparison.
Source: blueprint order 1276 (blueprint: proposition-proper-base-change-complete-integral--1). -/
def completedDerivedRestrictionDirectImageIso (n : ℕ) :
    pbcDerivedRestrict (pbcAdicProjection X d n) ⋙ completedDerivedDirectImage f d ≅
      completedFiniteDerivedDirectImage f d n ⋙
        pbcDerivedRestrict (pbcAdicProjection Y d n) :=
  (completedDerivedRestrictionDirectImageIso_exists f d n).exists.choose

/-- The finite projection-formula arrow is the scalar-adjunction mate of direct image
of the reduction unit, followed by the canonical restriction/direct-image comparison.
Source: blueprint order 1276 (blueprint: proposition-proper-base-change-complete-integral--1). -/
def completedDirectImageProjectionFormula (n : ℕ)
    (K : DerivedCategory (pbcModules X (pbcAdicCompletion X d))) :
    (pbcDerivedExtend (pbcAdicProjection Y d n)).obj
        ((completedDerivedDirectImage f d).obj K) ⟶
      (completedFiniteDerivedDirectImage f d n).obj
        ((pbcDerivedExtend (pbcAdicProjection X d n)).obj K) :=
  ((pbcDerivedScalarAdjunction (pbcAdicProjection Y d n)).homEquiv _ _).symm
    ((completedDerivedDirectImage f d).map
      ((pbcDerivedScalarAdjunction (pbcAdicProjection X d n)).unit.app K) ≫
      (completedDerivedRestrictionDirectImageIso f d n).hom.app
        ((pbcDerivedExtend (pbcAdicProjection X d n)).obj K))

private theorem scalarProjection_naturality
    {C D E B : Type*} [Category* C] [Category* D] [Category* E] [Category* B]
    {LX : C ⥤ D} {RX : D ⥤ C} {LY : E ⥤ B} {RY : B ⥤ E}
    (adjX : LX ⊣ RX) (adjY : LY ⊣ RY) (F : C ⥤ E) (G : D ⥤ B)
    (e : RX ⋙ F ≅ G ⋙ RY) {K L : C} (h : K ⟶ L) :
    LY.map (F.map h) ≫
        (adjY.homEquiv _ _).symm (F.map (adjX.unit.app L) ≫ e.hom.app (LX.obj L)) =
      (adjY.homEquiv _ _).symm (F.map (adjX.unit.app K) ≫ e.hom.app (LX.obj K)) ≫
        G.map (LX.map h) := by
  apply (adjY.homEquiv _ _).injective
  rw [adjY.homEquiv_naturality_left, adjY.homEquiv_naturality_right]
  simp only [Functor.id_obj, Equiv.apply_symm_apply]
  change F.map h ≫ (F.map (adjX.unit.app L) ≫ e.hom.app (LX.obj L)) =
    (F.map (adjX.unit.app K) ≫ e.hom.app (LX.obj K)) ≫ RY.map (G.map (LX.map h))
  rw [← Category.assoc, ← F.map_comp]
  have hu : h ≫ adjX.unit.app L = adjX.unit.app K ≫ RX.map (LX.map h) :=
    adjX.unit.naturality h
  rw [hu, F.map_comp, Category.assoc]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (F.map (adjX.unit.app K) ≫ ·) (e.hom.naturality (LX.map h))

private def restrictedUnitMap (T : Scheme.{u})
    {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : R ⟶ B) (a : S ⟶ B) (ha : φ ≫ a = ψ) :
    (pbcRestrict φ).obj (SheafOfModules.unit (reductionModuleRing T S)) ⟶
      (pbcRestrict ψ).obj (SheafOfModules.unit (reductionModuleRing T B)) :=
  ⟨PresheafOfModules.homMk
    (Functor.whiskerRight a.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}))
    (by
      intro U r m
      let m' : S.obj.obj U := m
      change (a.hom.app U).hom ((φ.hom.app U).hom r * m') =
        (ψ.hom.app U).hom r * (a.hom.app U).hom m'
      rw [map_mul]
      congr 1
      exact congrArg (fun z ↦ z.hom.app U r) ha)⟩

private def restrictedUnitIso (T : Scheme.{u})
    {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : R ⟶ B) (a : S ≅ B) (ha : φ ≫ a.hom = ψ) :
    (pbcRestrict φ).obj (SheafOfModules.unit (reductionModuleRing T S)) ≅
      (pbcRestrict ψ).obj (SheafOfModules.unit (reductionModuleRing T B)) where
  hom := restrictedUnitMap T φ ψ a.hom ha
  inv := restrictedUnitMap T ψ φ a.inv (by
    rw [← ha, Category.assoc, a.hom_inv_id, Category.comp_id])
  hom_inv_id := by
    ext U x
    exact congrArg (fun z ↦ z.hom.app U x) a.hom_inv_id
  inv_hom_id := by
    ext U x
    exact congrArg (fun z ↦ z.hom.app U x) a.inv_hom_id

private def completedQuotientModuleIso (T : Scheme.{u}) (n : ℕ) :
    (pbcRestrict ((pbcCompletedComparison T d).hom ≫ pbcAdicProjection T d n)).obj
        (SheafOfModules.unit (reductionModuleRing T ((pbcAdicRings T d).obj (op n)))) ≅
      CompletedConstantReduction.residue T d.ideal n :=
  (restrictedUnitIso T (limit.π (adicLisseRingSystem T d.ideal) (op n))
    ((pbcCompletedComparison T d).hom ≫ pbcAdicProjection T d n)
    (pbcLevelConstantComparison T d n) (by
      exact (HasLimit.isoOfNatIso_hom_π (pbcConstantSystemComparison T d) (op n)).symm)).symm

private theorem completedComplexUnit_eq
    (C : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ) :
    completedDirectImageComplexUnit f d C =
      (completedModuleDirectImage f d).rightDerivedFunctorUnitQ C := by
  simpa only [completedDirectImageComplexUnit, completedDerivedDirectImage] using
    Functor.rightDerivedComplexUnitNormalization (completedModuleDirectImage f d) C

private theorem finiteComplexUnit_eq (n : ℕ)
    (C : CochainComplex (pbcModules X ((pbcAdicRings X d).obj (op n))) ℤ) :
    completedFiniteDirectImageComplexUnit f d n C =
      (completedFiniteModuleDirectImage f d n).rightDerivedFunctorUnitQ C := by
  simpa only [completedFiniteDirectImageComplexUnit, completedFiniteDerivedDirectImage] using
    Functor.rightDerivedComplexUnitNormalization (completedFiniteModuleDirectImage f d n) C

set_option Elab.async false in
/-- Perfectness of each quotient makes this specified projection-formula arrow an
isomorphism, functorial in the input.
Source: blueprint order 1276; Stacks Project, Tag 0944.
(blueprint: lem-pbc-completed-direct-image-projection-properties).
Proof: identify the restricted finite-ring unit with the constant-system quotient
module by the canonical ring comparison and its limit-projection equation. The
scalar-to-tensor comparison identifies the specified arrow with the tensor projection.
The existing perfect projection formula applies because this quotient is perfect.
Cancel the comparison isomorphisms and reflect invertibility along exact restriction
of scalars, using its conservative action on homology. For naturality transpose the
equality through the scalar adjunction and use naturality of its unit and of the
restriction/direct-image comparison. -/
theorem completedDirectImageProjectionFormula_properties (d : AdicCoefficientDatum A) :
    (∀ (n : ℕ) (K : DerivedCategory (pbcModules X (pbcAdicCompletion X d))),
      IsIso (completedDirectImageProjectionFormula f d n K)) ∧
    ∀ (n : ℕ) (K L : DerivedCategory (pbcModules X (pbcAdicCompletion X d)))
      (h : K ⟶ L),
      (pbcDerivedExtend (pbcAdicProjection Y d n)).map
          ((completedDerivedDirectImage f d).map h) ≫
        completedDirectImageProjectionFormula f d n L =
      completedDirectImageProjectionFormula f d n K ≫
        (completedFiniteDerivedDirectImage f d n).map
          ((pbcDerivedExtend (pbcAdicProjection X d n)).map h) := by
  constructor
  · intro n K
    let := completedCoefficient_isIso f d
    let r := (DerivedCategory.singleFunctor (PerfectProjection.modules d Y) 0).mapIso
      (completedQuotientModuleIso d Y n)
    exact completedScalarProjectionPerfectIso f d
      ((pbcAdicRings Y d).obj (op n)) ((pbcAdicRings X d).obj (op n))
      (pbcAdicProjection Y d n) (pbcAdicProjection X d n)
      (asIso (completedFiniteCoefficientMap f d n)) (limit.lift_π _ (op n))
      (completedModuleDirectImage f d) rfl (completedFiniteModuleDirectImage f d n) rfl
      (completedRestrictionDirectImageIso f d n)
      (by
        intro M U
        apply heq_of_eq
        funext x
        exact (completedRestrictionDirectImageIso_exists f d n).exists.choose_spec M U x)
      (completedDerivedRestrictionDirectImageIso f d n)
      (by
        intro J
        simpa only [finiteComplexUnit_eq, completedComplexUnit_eq,
          completedDerivedRestrictionDirectImageIso,
          completedDerivedDirectImage, completedFiniteDerivedDirectImage] using
          (completedDerivedRestrictionDirectImageIso_exists f d n).exists.choose_spec J)
      n r K
  · intro n K L h
    exact scalarProjection_naturality
      (pbcDerivedScalarAdjunction (pbcAdicProjection X d n))
      (pbcDerivedScalarAdjunction (pbcAdicProjection Y d n))
      (completedDerivedDirectImage f d) (completedFiniteDerivedDirectImage f d n)
      (completedDerivedRestrictionDirectImageIso f d n) h

end AlgebraicGeometry.Scheme
