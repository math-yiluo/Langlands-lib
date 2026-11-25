/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.CategoryTheory.ExactProductsRoos.ExactProductsRoosComparisonSupplement
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.CategoryTheory.Ringed.RingedTowerPushforwardLimitComparison
import WeilConjectures.CategoryTheory.Strict.StrictRoosAdditiveComparison
import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective

/-! # Normalized direct image of canonical Roos triangles

Source: Stacks Project, Cohomology on Sites, Tags 0A07 and 0941; Derived Categories,
Tag 0BK6, with the explicit strict cone normalization in the DAG
(blueprint: lem-weil-pbc-direct-image-roos-normalization).

The structures below only package the choices of total derived functors, units and
canonical comparisons already appearing in the statement. The conclusion constructs
Roos triangles with normalization on every complex, rather than choosing cone vertices
up to an unspecified isomorphism. The index `n : ℕ` denotes positive level `n + 1`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w uA vA uB vB g

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace CategoryTheory
namespace DirectImageRoosNormalization

section PrivateElementary

set_option backward.isDefEq.respectTransparency false
attribute [local instance] Abelian.hasFiniteBiproducts

end PrivateElementary

variable (A : Type uA) [Category.{vA} A] [Abelian A]
  [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory.{w} A]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]

/-- Total derived inverse limit and evaluation of strict towers, with their units.
Source: Stacks Tags 0940 and 0941
(blueprint: lem-weil-pbc-direct-image-roos-normalization).
This packages the interface of `ringedStrictTowerHomotopyLimitIndependentCoefficients`.
It introduces no new inverse-limit or evaluation construction. -/
structure LimitData where
  limit : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A
  unit : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ) ⋙
    DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ limit
  derived : limit.IsRightDerivedFunctor unit
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))
  unit_isIso : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, I.IsKInjective → IsIso (unit.app I)
  evaluation : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ DerivedCategory.{w} A)
  evaluationIso : DerivedCategory.Q ⋙ evaluation ≅
    HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (Functor.whiskeringRight ℕᵒᵖ (CochainComplex A ℤ)
        (DerivedCategory.{w} A)).obj DerivedCategory.Q

variable {A}
variable {B : Type uB} [Category.{vB} B] [Abelian B]
  [HasLimitsOfShape ℕᵒᵖ B] [HasDerivedCategory.{w} B]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]

/-- The normalized derived direct-image comparison of strict inverse limits.
Source: Stacks Tag 0A07 and the common-underived-composite normalization
(blueprint: lem-weil-pbc-direct-image-roos-normalization).
The fields are precisely choices in `ringedTowerPushforwardLimitComparison`.
`ordinary_components` fixes the underived comparison; `comparison_unit` fixes `a`.
The evaluation comparison is fixed on K-injectives, including all transitions. -/
structure DirectImageData (G : A ⥤ B) [G.Additive] where
  source : LimitData.{w} A
  target : LimitData.{w} B
  direct : DerivedCategory.{w} A ⥤ DerivedCategory.{w} B
  tower : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} (ℕᵒᵖ ⥤ B)
  unit : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ direct
  towerUnit : ((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ) ⋙
    DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ tower
  direct_derived : direct.IsRightDerivedFunctor unit
    (HomologicalComplex.quasiIso A (.up ℤ))
  tower_derived : tower.IsRightDerivedFunctor towerUnit
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))
  unit_isIso : ∀ I : CochainComplex A ℤ, I.IsKInjective → IsIso (unit.app I)
  towerUnit_isIso : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    I.IsKInjective → IsIso (towerUnit.app I)
  ordinary : (lim : (ℕᵒᵖ ⥤ A) ⥤ A) ⋙ G ≅
    (Functor.whiskeringRight ℕᵒᵖ A B).obj G ⋙ (lim : (ℕᵒᵖ ⥤ B) ⥤ B)
  ordinary_components : ∀ (H : ℕᵒᵖ ⥤ A) (n : ℕᵒᵖ),
    ordinary.hom.app H ≫ limit.π (H ⋙ G) n = G.map (limit.π H n)
  comparison : source.limit ⋙ direct ≅ tower ⋙ target.limit
  comparison_unit : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    unit.app (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj X) ≫
        direct.map (source.unit.app X) ≫ comparison.hom.app (DerivedCategory.Q.obj X) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app X) ≫
        target.unit.app
          ((((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)).obj X) ≫
        target.limit.map (towerUnit.app X)
  evaluationIso : tower ⋙ target.evaluation ≅ source.evaluation ⋙
    (Functor.whiskeringRight ℕᵒᵖ (DerivedCategory.{w} A) (DerivedCategory.{w} B)).obj direct
  evaluation_unit : ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ), I.IsKInjective → ∀ n : ℕᵒᵖ,
    (target.evaluation.map (towerUnit.app I)).app n ≫
        (evaluationIso.hom.app (DerivedCategory.Q.obj I)).app n ≫
        direct.map ((source.evaluationIso.hom.app I).app n) =
      (target.evaluationIso.hom.app
        ((((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)).obj I)).app n ≫
        unit.app (I.asFunctor.obj n)

variable [HasCountableProducts A] [HasCountableProducts (DerivedCategory.{w} A)]

/-- The ordinary-limit inclusion into the existing strict Roos cone, with coordinates
`(0, (λ_n)_n)`. Source: Stacks Tag 0941
(blueprint: lem-weil-pbc-direct-image-roos-normalization).
The domain is termwise ordinary limit, as in the total-derived-functor unit. -/
def ordinaryInclusion (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (ExactProductsRoos.ordinary (B := A)).obj X ⟶ roosF.obj X :=
  roosLift (ExactProductsRoos.inclusion.app X) (ExactProductsRoos.inclusion_difference X)

section PrivateComparisons

set_option backward.isDefEq.respectTransparency false
attribute [local instance] Abelian.hasFiniteBiproducts


set_option backward.isDefEq.respectTransparency false in
omit [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory A]
  [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasCountableProducts A]
  [HasCountableProducts (DerivedCategory A)] in
private theorem coneArrowMap_eq
    {X Y X' Y' : CochainComplex A ℤ} (f : X ⟶ Y) (g : X' ⟶ Y')
    (α : Arrow.mk f ⟶ Arrow.mk g) : HomologicalComplex.homotopyCofiber.mapArrowHom f g
    (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) α =
      CochainComplex.mappingCone.map f g α.left α.right α.w.symm := by
  ext n : 1
  apply HomologicalComplex.homotopyCofiber.ext_from_X f (n + 1) n rfl
  · simp only [HomologicalComplex.homotopyCofiber.mapArrowHom,
      HomologicalComplex.homotopyCofiber.inlX_desc_f,
      Homotopy.trans_hom, Homotopy.ofEq_hom, Homotopy.compLeft_hom,
      Pi.zero_apply, zero_add, add_zero,
      ]
    change _ = (CochainComplex.mappingCone.inl f).v (n + 1) n (by omega) ≫
      (CochainComplex.mappingCone.map f g α.left α.right α.w.symm).f n
    unfold CochainComplex.mappingCone.map
    rw [CochainComplex.mappingCone.inl_v_desc_f,
      CochainComplex.HomComplex.Cochain.comp_v _ _ _ (n + 1) (n + 1) n (by omega) (by omega)]
    rw [HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom _ _ (n + 1) n rfl]
    simp only [CochainComplex.HomComplex.Cochain.ofHom_v,
      CochainComplex.mappingCone.inl, CochainComplex.HomComplex.Cochain.mk_v]
  · simp only [HomologicalComplex.homotopyCofiber.mapArrowHom,
      HomologicalComplex.homotopyCofiber.inrX_desc_f]
    change _ = (CochainComplex.mappingCone.inr f).f n ≫
      (CochainComplex.mappingCone.map f g α.left α.right α.w.symm).f n
    unfold CochainComplex.mappingCone.map
    rw [CochainComplex.mappingCone.inr_f_desc_f]
    rfl

@[irreducible]
private def roosSignComponent (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    ExactProductsRoos.fibre.obj X ≅ roosF.obj X :=
  (shiftFunctor _ (-1 : ℤ)).mapIso
    (HomologicalComplex.homotopyCofiber.mapArrowIso _ _
      (fun j : ℤ ↦ ⟨j - 1, sub_add_cancel j 1⟩)
      (Arrow.isoMk (Iso.refl _) (-(Iso.refl _)) (by simp)))

omit [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)]
  [HasCountableProducts (DerivedCategory A)] in
private theorem roosF_map_arrow {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : X ⟶ Y) :
    roosF.map f =
      (HomologicalComplex.homotopyCofiber.mapArrowHom _ _
        (fun j : ℤ ↦ ⟨j - 1, sub_add_cancel j 1⟩)
        (Arrow.homMk (roosPmap f) (roosPmap f) (roosU_natural f).symm))⟦(-1 : ℤ)⟧' := by
  rw [coneArrowMap_eq]
  rfl

private def roosSign :
    Iso (C := CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex A ℤ)
      ExactProductsRoos.fibre roosF :=
  NatIso.ofComponents (fun X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ ↦ roosSignComponent X) (by
    intro X Y f
    let H : ∀ j : ℤ, ∃ i, (ComplexShape.up ℤ).Rel i j :=
      fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩
    let a (Z : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
        Arrow.mk (-roosU Z) ≅ Arrow.mk (roosU Z) :=
      Arrow.isoMk (Iso.refl _) (-(Iso.refl _)) (by simp)
    let β : Arrow.mk (roosU X) ⟶ Arrow.mk (roosU Y) :=
      Arrow.homMk (roosPmap f) (roosPmap f) (roosU_natural f).symm
    have h : ExactProductsRoos.arrowMap f ≫ (a Y).hom = (a X).hom ≫ β := by
      apply Arrow.hom_ext <;> simp [a, β, ExactProductsRoos.arrowMap,
        Arrow.isoMk, roosPmap, ExactProductsRoos.product]
    rw [roosF_map_arrow]
    unfold roosSignComponent
    change (shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map
        (HomologicalComplex.homotopyCofiber.mapArrowHom _ _ H
          (ExactProductsRoos.arrowMap f)) ≫
        (shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map
          (HomologicalComplex.homotopyCofiber.mapArrowHom _ _ H (a Y).hom) =
      (shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map
        (HomologicalComplex.homotopyCofiber.mapArrowHom _ _ H (a X).hom) ≫
        (shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map
          (HomologicalComplex.homotopyCofiber.mapArrowHom _ _ H β)
    rw [← Functor.map_comp, ← Functor.map_comp]
    apply congrArg ((shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map)
    exact (HomologicalComplex.homotopyCofiber.mapArrowHom_comp
      (-roosU X) (-roosU Y) (roosU Y) H (ExactProductsRoos.arrowMap f) (a Y).hom).symm.trans
      ((congrArg (HomologicalComplex.homotopyCofiber.mapArrowHom
        (-roosU X) (roosU Y) H) h).trans
        (HomologicalComplex.homotopyCofiber.mapArrowHom_comp
          (-roosU X) (roosU X) (roosU Y) H (a X).hom β)))

set_option backward.isDefEq.respectTransparency false in
omit [HasDerivedCategory A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)]
  [HasCountableProducts (DerivedCategory A)] in
private theorem ordinaryInclusion_f (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (ordinaryInclusion X).f p = (ExactProductsRoos.inclusion.app X).f p ≫
      HomologicalComplex.homotopyCofiber.inlX (roosU X) p (p + (-1))
        (by change p + (-1) + 1 = p; omega) := by
  simp only [ordinaryInclusion, roosLift, CochainComplex.mappingCocone.lift,
    CochainComplex.mappingCocone.liftCocycle, CochainComplex.mappingCocone.liftCochain,
    CochainComplex.mappingCone.liftCochain,
    CochainComplex.HomComplex.Cocycle.ofHom_coe, CochainComplex.mappingCone.inl,
    CochainComplex.mappingCone.inr, CochainComplex.HomComplex.Cochain.zero_comp,
    add_zero, CochainComplex.HomComplex.Cocycle.homOf_f,
    CochainComplex.HomComplex.Cochain.rightShift_v (n := -1)
      _ _ _ _ p _ _ (p + (-1)) (by omega),
    CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
    CochainComplex.HomComplex.Cochain.ofHom_v, CochainComplex.HomComplex.Cochain.mk_v,
    CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_inv, Category.assoc]
  rw [Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
omit [HasDerivedCategory A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasCountableProducts (DerivedCategory
  A)] in
private theorem roosSign_inclusion (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    ExactProductsRoos.comparison.app X ≫ roosSign.hom.app X = ordinaryInclusion X := by
  ext p : 1
  change (ExactProductsRoos.comparisonApp X).f p ≫
    (roosSignComponent X).hom.f p = _
  rw [ExactProductsRoos.comparisonApp_f, ordinaryInclusion_f]
  simp only [roosSignComponent, Functor.mapIso_hom,
    HomologicalComplex.homotopyCofiber.mapArrowIso_hom]
  rw [CochainComplex.shiftFunctor_map_f']
  rw [Category.assoc]
  dsimp only [HomologicalComplex.homotopyCofiber.mapArrowHom]
  rw [
    HomologicalComplex.homotopyCofiber.inlX_desc_f]
  simp only [Homotopy.trans_hom, Homotopy.ofEq_hom, Homotopy.compLeft_hom,
    Pi.zero_apply, zero_add, add_zero]
  rw [HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom]
  · simp
  · change p + -1 + 1 = p
    omega

omit [HasDerivedCategory A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasCountableProducts (DerivedCategory
  A)] in
private theorem ordinaryInclusion_χ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (ordinaryInclusion X).f (p + 1) ≫ (roosχ X p).hom =
      biprod.lift 0 ((ExactProductsRoos.inclusion.app X).f (p + 1)) :=
  roosLift_χ _ _ p

omit [HasDerivedCategory A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasCountableProducts (DerivedCategory
  A)] in
private theorem ordinaryInclusion_projection (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    ordinaryInclusion X ≫ roosProj X = ExactProductsRoos.inclusion.app X := by
  apply HomologicalComplex.hom_ext
  intro k
  obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
  change (ordinaryInclusion X ≫ roosProj X).f (p + 1) =
    (ExactProductsRoos.inclusion.app X).f (p + 1)
  simp only [HomologicalComplex.comp_f, roosProj_f, ← Category.assoc,
    ordinaryInclusion_χ, biprod.lift_snd]

private def roosProjection : roosF ⟶ ExactProductsRoos.product (B := A) where
  app X := roosProj X
  naturality X Y f := by
    change roosF.map f ≫ roosProj Y = roosProj X ≫ roosPmap f
    apply Pi.hom_ext
    intro n
    simpa only [roosEval, roosPmap, Category.assoc, Pi.map_π] using
      roosEval_natural f n

private def roosBoundary :
    ExactProductsRoos.product (B := A) ⟶ roosF ⋙ shiftFunctor _ (1 : ℤ) where
  app X := (CochainComplex.mappingCocone.triangle (roosU X)).mor₃
  naturality X Y f := by
    dsimp only [CochainComplex.mappingCocone.triangle,
      CochainComplex.mappingCone.triangle, Triangle.mk, Functor.comp_map]
    simp only [Category.assoc]
    let e := shiftFunctorCompIsoId (CochainComplex A ℤ) (-1 : ℤ) 1 (by omega)
    change roosPmap f ≫ CochainComplex.mappingCone.inr (roosU Y) ≫
        e.inv.app (CochainComplex.mappingCone (roosU Y)) =
      CochainComplex.mappingCone.inr (roosU X) ≫
        e.inv.app (CochainComplex.mappingCone (roosU X)) ≫
        (roosF.map f)⟦(1 : ℤ)⟧'
    rw [← Category.assoc,
      show roosPmap f ≫ CochainComplex.mappingCone.inr (roosU Y) =
        CochainComplex.mappingCone.inr (roosU X) ≫ roosConeFunctor.map f from
          (CochainComplex.mappingCone.triangleMap (roosU X) (roosU Y)
            (roosPmap f) (roosPmap f) (roosU_natural f)).comm₂.symm, Category.assoc]
    congr 1
    exact e.inv.naturality (roosConeFunctor.map f)

set_option backward.defeqAttrib.useBackward true in
omit [HasCountableProducts (DerivedCategory A)] in
private theorem normalizedConeComparison
    [IsGrothendieckAbelian.{g} (ℕᵒᵖ ⥤ A)]
    [HasExactLimitsOfShape (Discrete ℕ) A] (L : LimitData.{w} A) :
    ∃ e : roosF (A := A) ⋙ DerivedCategory.Q ≅
      (DerivedCategory.Q (C := ℕᵒᵖ ⥤ A)) ⋙ L.limit,
      ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        DerivedCategory.Q.map (ordinaryInclusion X) ≫ e.hom.app X = L.unit.app X := by
  obtain ⟨e, he⟩ := ExactProductsRoos.comparisonIso L.limit L.unit L.unit_isIso
  refine ⟨Functor.isoWhiskerRight roosSign.symm DerivedCategory.Q ≪≫ e, ?_⟩
  intro X
  have hs : ordinaryInclusion X ≫ roosSign.inv.app X =
      ExactProductsRoos.comparison.app X := by
    rw [← roosSign_inclusion X]
    simp
  change DerivedCategory.Q.map (ordinaryInclusion X) ≫
      DerivedCategory.Q.map (roosSign.inv.app X) ≫ e.hom.app X = _
  rw [← DerivedCategory.Q.map_comp_assoc, hs]
  exact congr_app he X

private def derivedProducts :
    (ℕᵒᵖ ⥤ DerivedCategory.{w} A) ⥤ DerivedCategory.{w} A where
  obj M := ∏ᶜ (fun n : ℕ ↦ M.obj (op n))
  map f := Limits.Pi.map (fun n : ℕ ↦ f.app (op n))
  map_id M := by
    apply Pi.hom_ext
    intro n
    simp
  map_comp f k := by simp [Limits.Pi.map_comp_map]

end PrivateComparisons

/-- The canonical Roos triangle, specified on every representing complex.
Source: Stacks Tags 0941 and 0A07, with the DAG's explicit cone convention
(blueprint: lem-weil-pbc-direct-image-roos-normalization).
`normalization` characterizes the comparison with total derived limit by its unit.
It is equivalently the exact-products fibre comparison followed by `(y,x) ↦ (-y,x)`:
both carry the ordinary-limit inclusion to that unit. The last two fields transport
exactly the first and connecting arrows of the rotated strict cone triangle. -/
structure RoosTriangleData (L : LimitData.{w} A) where
  projection : ∀ M, L.limit.obj M ⟶ ∏ᶜ (fun n : ℕ ↦ (L.evaluation.obj M).obj (op n))
  boundary : ∀ M, (∏ᶜ (fun n : ℕ ↦ (L.evaluation.obj M).obj (op n))) ⟶
    (L.limit.obj M)⟦(1 : ℤ)⟧
  distinguished : ∀ M, IsDerivedLimitTriangle
    (fun n : ℕ ↦ (L.evaluation.obj M).map (homOfLE (Nat.le_succ n)).op)
    (L.limit.obj M) (projection M) (boundary M)
  projection_natural : ∀ {M N} (f : M ⟶ N),
    L.limit.map f ≫ projection N = projection M ≫
      Limits.Pi.map (fun n : ℕ ↦ (L.evaluation.map f).app (op n))
  boundary_natural : ∀ {M N} (f : M ⟶ N),
    Limits.Pi.map (fun n : ℕ ↦ (L.evaluation.map f).app (op n)) ≫ boundary N =
      boundary M ≫ (L.limit.map f)⟦(1 : ℤ)⟧'
  coneComparison : roosF ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ L.limit
  normalization : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    DerivedCategory.Q.map (ordinaryInclusion X) ≫ coneComparison.hom.app X = L.unit.app X
  productComparison : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    DerivedCategory.Q.obj (roosP X) ≅
      ∏ᶜ (fun n : ℕ ↦ (L.evaluation.obj (DerivedCategory.Q.obj X)).obj (op n))
  product_components : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ),
    (productComparison X).hom ≫ Pi.π _ n =
      DerivedCategory.Q.map (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n) ≫
        (L.evaluationIso.inv.app X).app (op n)
  projection_model : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    coneComparison.hom.app X ≫ projection (DerivedCategory.Q.obj X) =
      DerivedCategory.Q.map (roosProj X) ≫ (productComparison X).hom
  boundary_model : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    (productComparison X).hom ≫ boundary (DerivedCategory.Q.obj X) =
      DerivedCategory.Q.map (CochainComplex.mappingCocone.triangle (roosU X)).mor₃ ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (roosF.obj X) ≫
        (coneComparison.hom.app X)⟦(1 : ℤ)⟧'

section PrivateTriangles

set_option backward.isDefEq.respectTransparency false
attribute [local instance] Abelian.hasFiniteBiproducts


private theorem projection_unit (L : LimitData.{w} A) (T : RoosTriangleData L)
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    L.unit.app X ≫ T.projection (DerivedCategory.Q.obj X) =
      DerivedCategory.Q.map (ExactProductsRoos.inclusion.app X) ≫
        (T.productComparison X).hom := by
  rw [← T.normalization X, Category.assoc, T.projection_model,
    ← DerivedCategory.Q.map_comp_assoc, ordinaryInclusion_projection]

private def projectionNat {L : LimitData.{w} A} (T : RoosTriangleData L) :
    L.limit ⟶ L.evaluation ⋙ derivedProducts where
  app := T.projection
  naturality _ _ f := T.projection_natural f

end PrivateTriangles

variable [HasCountableProducts (DerivedCategory.{w} B)]

/-- The product comparison whose components are the images of product projections.
Source: Stacks Tag 0A07 (blueprint: lem-weil-pbc-direct-image-roos-normalization). -/
def alpha {G : A ⥤ B} [G.Additive] (d : DirectImageData G)
    (M : DerivedCategory.{w} (ℕᵒᵖ ⥤ A)) :=
  piComparison d.direct (fun n : ℕ ↦ (d.source.evaluation.obj M).obj (op n))

/-- The same product comparison with its target identified by derived strict evaluation.
Source: Stacks Tag 0A07 (blueprint: lem-weil-pbc-direct-image-roos-normalization). -/
def productMap {G : A ⥤ B} [G.Additive] (d : DirectImageData G)
    (M : DerivedCategory.{w} (ℕᵒᵖ ⥤ A)) :
    d.direct.obj (∏ᶜ (fun n : ℕ ↦ (d.source.evaluation.obj M).obj (op n))) ⟶
      ∏ᶜ (fun n : ℕ ↦ (d.target.evaluation.obj (d.tower.obj M)).obj (op n)) :=
  alpha d M ≫ Limits.Pi.map (fun n : ℕ ↦ (d.evaluationIso.inv.app M).app (op n))

variable [HasCountableProducts B]

section PrivateSquares

set_option backward.isDefEq.respectTransparency false
attribute [local instance] Abelian.hasFiniteBiproducts


omit [HasCountableProducts A] [HasCountableProducts B] in
@[reassoc]
private theorem productMap_π {G : A ⥤ B} [G.Additive] (d : DirectImageData G)
    (M : DerivedCategory.{w} (ℕᵒᵖ ⥤ A)) (n : ℕ) :
    productMap d M ≫ Pi.π _ n =
      d.direct.map (Pi.π _ n) ≫ (d.evaluationIso.inv.app M).app (op n) := by
  simp only [productMap, alpha, Category.assoc, Pi.map_π, piComparison_comp_π_assoc]

omit [HasCountableProducts A] [HasCountableProducts (DerivedCategory A)]
  [HasCountableProducts (DerivedCategory B)] [HasCountableProducts B] in
@[reassoc]
private theorem unit_naturality {G : A ⥤ B} [G.Additive] (d : DirectImageData G)
    {X Y : CochainComplex A ℤ} (f : X ⟶ Y) :
    DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map f) ≫ d.unit.app Y =
      d.unit.app X ≫ d.direct.map (DerivedCategory.Q.map f) :=
  d.unit.naturality f

omit [HasCountableProducts A] [HasCountableProducts (DerivedCategory A)] [HasCountableProducts
  (DerivedCategory B)] [HasCountableProducts B] in
private theorem evaluation_unit_inv {G : A ⥤ B} [G.Additive]
    (d : DirectImageData G) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective]
    (n : ℕᵒᵖ) :
    d.unit.app (I.asFunctor.obj n) ≫
        d.direct.map ((d.source.evaluationIso.inv.app I).app n) ≫
        (d.evaluationIso.inv.app (DerivedCategory.Q.obj I)).app n =
      (d.target.evaluationIso.inv.app
        ((((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)).obj I)).app n ≫
        (d.target.evaluation.map (d.towerUnit.app I)).app n := by
  let J : CochainComplex (ℕᵒᵖ ⥤ B) ℤ :=
    (((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)).obj I
  let eS : (d.source.evaluation.obj (DerivedCategory.Q.obj I)).obj n ≅
      DerivedCategory.Q.obj (I.asFunctor.obj n) := (d.source.evaluationIso.app I).app n
  let eT : (d.target.evaluation.obj (DerivedCategory.Q.obj J)).obj n ≅
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj
        (I.asFunctor.obj n)) := (d.target.evaluationIso.app J).app n
  let e : (d.target.evaluation.obj (d.tower.obj (DerivedCategory.Q.obj I))).obj n ≅
      d.direct.obj ((d.source.evaluation.obj (DerivedCategory.Q.obj I)).obj n) :=
    (d.evaluationIso.app (DerivedCategory.Q.obj I)).app n
  let τ : (d.target.evaluation.obj (DerivedCategory.Q.obj J)).obj n ⟶
      (d.target.evaluation.obj (d.tower.obj (DerivedCategory.Q.obj I))).obj n :=
    (d.target.evaluation.map (d.towerUnit.app I)).app n
  let η : DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj
      (I.asFunctor.obj n)) ⟶ d.direct.obj (DerivedCategory.Q.obj (I.asFunctor.obj n)) :=
    d.unit.app (I.asFunctor.obj n)
  have h : τ ≫ e.hom ≫ d.direct.map eS.hom = eT.hom ≫ η :=
    d.evaluation_unit I inferInstance n
  change η ≫ d.direct.map eS.inv ≫ e.inv = eT.inv ≫ τ
  calc
    _ = eT.inv ≫ (eT.hom ≫ η) ≫ d.direct.map eS.inv ≫ e.inv := by
      simp only [Category.assoc, eT.inv_hom_id_assoc]
    _ = eT.inv ≫ (τ ≫ e.hom ≫ d.direct.map eS.hom) ≫
        d.direct.map eS.inv ≫ e.inv := by rw [h]
    _ = _ := by
      simp only [Category.assoc, ← d.direct.map_comp_assoc, eS.hom_inv_id,
        Functor.map_id, Category.id_comp, e.hom_inv_id, Category.comp_id]

private theorem productMap_unit {G : A ⥤ B} [G.Additive]
    (d : DirectImageData G) (T : RoosTriangleData d.source)
    (U : RoosTriangleData d.target) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    [I.IsKInjective] :
    d.unit.app (roosP I) ≫ d.direct.map (T.productComparison I).hom ≫
        productMap d (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map (piComparison (G.mapHomologicalComplex (.up ℤ))
        (fun n : ℕ ↦ I.asFunctor.obj (op n))) ≫
        (U.productComparison
          ((((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)).obj I)).hom ≫
          Limits.Pi.map (fun n : ℕ ↦
            (d.target.evaluation.map (d.towerUnit.app I)).app (op n)) := by
  let J : CochainComplex (ℕᵒᵖ ⥤ B) ℤ :=
    (((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)).obj I
  have hπ (n : ℕ) :
      Limits.Pi.map (fun k : ℕ ↦
          (d.target.evaluation.map (d.towerUnit.app I)).app (op k)) ≫
        Pi.π (fun k : ℕ ↦
          (d.target.evaluation.obj (d.tower.obj (DerivedCategory.Q.obj I))).obj (op k)) n =
      Pi.π (fun k : ℕ ↦
          (d.target.evaluation.obj (DerivedCategory.Q.obj J)).obj (op k)) n ≫
        (d.target.evaluation.map (d.towerUnit.app I)).app (op n) :=
    Pi.map_π _ n
  have hc (n : ℕ) :
      piComparison (G.mapHomologicalComplex (.up ℤ))
          (fun k : ℕ ↦ I.asFunctor.obj (op k)) ≫
        Pi.π (fun k : ℕ ↦ J.asFunctor.obj (op k)) n =
      (G.mapHomologicalComplex (.up ℤ)).map
        (Pi.π (fun k : ℕ ↦ I.asFunctor.obj (op k)) n) :=
    piComparison_comp_π _ _ n
  dsimp only [J] at hπ hc
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, productMap_π, hπ]
  rw [← d.direct.map_comp_assoc, T.product_components, d.direct.map_comp]
  simp only [Category.assoc]
  rw [← unit_naturality_assoc d (Pi.π (fun k : ℕ ↦ I.asFunctor.obj (op k)) n),
    evaluation_unit_inv]
  rw [reassoc_of% U.product_components, ← DerivedCategory.Q.map_comp_assoc, hc]

set_option backward.isDefEq.respectTransparency.types false in
omit [HasCountableProducts (DerivedCategory A)] [HasCountableProducts (DerivedCategory B)] in
private theorem ordinary_product_square {G : A ⥤ B} [G.Additive]
    (d : DirectImageData G) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (G.mapHomologicalComplex (.up ℤ)).map (ExactProductsRoos.inclusion.app I) ≫
        piComparison (G.mapHomologicalComplex (.up ℤ))
          (fun n : ℕ ↦ I.asFunctor.obj (op n)) =
      (NatTrans.mapHomologicalComplex d.ordinary.hom (.up ℤ)).app I ≫
        ExactProductsRoos.inclusion.app
          ((((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)).obj I) := by
  apply Pi.hom_ext (f := fun n : ℕ ↦
    (HomologicalComplex.asFunctor
      ((((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)).obj I)).obj (op n))
  intro n
  have h : piComparison (G.mapHomologicalComplex (.up ℤ))
        (fun k : ℕ ↦ I.asFunctor.obj (op k)) ≫
      Pi.π (fun k : ℕ ↦
        (HomologicalComplex.asFunctor
          ((((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)).obj I)).obj
          (op k)) n =
      (G.mapHomologicalComplex (.up ℤ)).map
        (Pi.π (fun k : ℕ ↦ I.asFunctor.obj (op k)) n) :=
    piComparison_comp_π _ _ n
  rw [Category.assoc, h, ← Functor.map_comp]
  simp only [Category.assoc, Pi.lift_comp_π]
  ext p
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f]
  exact (d.ordinary_components (I.X p) (op n)).symm

set_option backward.isDefEq.respectTransparency.types false in
private theorem projection_square_on_KInjective {G : A ⥤ B} [G.Additive]
    (d : DirectImageData G) (T : RoosTriangleData d.source)
    (U : RoosTriangleData d.target) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    [I.IsKInjective] :
    d.direct.map (T.projection (DerivedCategory.Q.obj I)) ≫
        productMap d (DerivedCategory.Q.obj I) =
      d.comparison.hom.app (DerivedCategory.Q.obj I) ≫
        U.projection (d.tower.obj (DerivedCategory.Q.obj I)) := by
  have : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive :=
    Functor.additive_of_preserves_binary_products _
  let : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).PreservesKInjectiveComplexes :=
    Adjunction.preservesKInjectiveComplexes constLimAdj
  let := d.source.unit_isIso I inferInstance
  let := d.unit_isIso (ExactProductsRoos.ordinary.obj I) inferInstance
  apply (cancel_epi (d.unit.app (ExactProductsRoos.ordinary.obj I) ≫
    d.direct.map (d.source.unit.app I))).mp
  let J := (((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)).obj I
  calc
    _ = DerivedCategory.Q.map
        ((G.mapHomologicalComplex (.up ℤ)).map (ExactProductsRoos.inclusion.app I)) ≫
          d.unit.app (roosP I) ≫ d.direct.map (T.productComparison I).hom ≫
            productMap d (DerivedCategory.Q.obj I) := by
      simp only [Category.assoc]
      rw [← d.direct.map_comp_assoc,
        projection_unit, d.direct.map_comp]
      simp only [Category.assoc]
      rw [← unit_naturality_assoc d]
    _ = DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex d.ordinary.hom (.up ℤ)).app I) ≫
          DerivedCategory.Q.map (ExactProductsRoos.inclusion.app J) ≫
            (U.productComparison J).hom ≫
              Limits.Pi.map (fun n : ℕ ↦
                (d.target.evaluation.map (d.towerUnit.app I)).app (op n)) := by
      rw [productMap_unit d T U I, ← DerivedCategory.Q.map_comp_assoc,
        ordinary_product_square d I, DerivedCategory.Q.map_comp]
      dsimp only [J]
      simp only [Category.assoc]
    _ = DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex d.ordinary.hom (.up ℤ)).app I) ≫
          d.target.unit.app J ≫ d.target.limit.map (d.towerUnit.app I) ≫
            U.projection (d.tower.obj (DerivedCategory.Q.obj I)) := by
      have hn : d.target.limit.map (d.towerUnit.app I) ≫
          U.projection (d.tower.obj (DerivedCategory.Q.obj I)) =
          U.projection (DerivedCategory.Q.obj J) ≫
            Limits.Pi.map (fun n : ℕ ↦
              (d.target.evaluation.map (d.towerUnit.app I)).app (op n)) :=
        U.projection_natural (d.towerUnit.app I)
      dsimp only [J] at hn ⊢
      rw [hn]
      simpa only [Category.assoc] using congrArg
        (fun f ↦ DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex d.ordinary.hom (.up ℤ)).app I) ≫ f ≫
            Limits.Pi.map (fun n : ℕ ↦
              (d.target.evaluation.map (d.towerUnit.app I)).app (op n)))
        (projection_unit d.target U J).symm
    _ = _ := by
      dsimp only [J]
      simp only [Category.assoc]
      rw [← reassoc_of% d.comparison_unit I]

omit [HasCountableProducts A] [HasCountableProducts B] in
private theorem productMap_naturality {G : A ⥤ B} [G.Additive]
    (d : DirectImageData G) {M N : DerivedCategory.{w} (ℕᵒᵖ ⥤ A)} (f : M ⟶ N) :
    d.direct.map (Limits.Pi.map
        (fun n : ℕ ↦ (d.source.evaluation.map f).app (op n))) ≫ productMap d N =
      productMap d M ≫ Limits.Pi.map
        (fun n : ℕ ↦ (d.target.evaluation.map (d.tower.map f)).app (op n)) := by
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, productMap_π, productMap_π_assoc, Pi.map_π]
  rw [← d.direct.map_comp_assoc, Pi.map_π, d.direct.map_comp, Category.assoc]
  congr 1
  exact congr_app (d.evaluationIso.inv.naturality f) (op n)

omit [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory A]
  [HasCountableProducts A] [HasCountableProducts (DerivedCategory A)] in
private theorem derivedNatTrans_ext_on_KInjectives
    [IsGrothendieckAbelian.{g} (ℕᵒᵖ ⥤ A)]
    {E : Type*} [Category E] {F₁ F₂ : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ E}
    (τ τ' : F₁ ⟶ F₂)
    (h : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, I.IsKInjective →
      τ.app (DerivedCategory.Q.obj I) = τ'.app (DerivedCategory.Q.obj I)) : τ = τ' := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))
  intro X
  let q := (CochainComplex.toKInjectiveResolution.{g} (ℕᵒᵖ ⥤ A)).app X
  let : QuasiIso q :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{g} (ℕᵒᵖ ⥤ A) X).2
  apply (cancel_mono (F₂.map (DerivedCategory.Q.map q))).mp
  rw [← τ.naturality, ← τ'.naturality, h _ inferInstance]

private def productTransformation {G : A ⥤ B} [G.Additive]
    (d : DirectImageData G) :
    d.source.evaluation ⋙ derivedProducts ⋙ d.direct ⟶
      d.tower ⋙ d.target.evaluation ⋙ derivedProducts where
  app := productMap d
  naturality _ _ f := productMap_naturality d f

private theorem projection_square {G : A ⥤ B} [G.Additive]
    [IsGrothendieckAbelian.{g} (ℕᵒᵖ ⥤ A)]
    (d : DirectImageData G) (T : RoosTriangleData d.source)
    (U : RoosTriangleData d.target) (M : DerivedCategory.{w} (ℕᵒᵖ ⥤ A)) :
    d.direct.map (T.projection M) ≫ productMap d M =
      d.comparison.hom.app M ≫ U.projection (d.tower.obj M) := by
  have h : Functor.whiskerRight (projectionNat T) d.direct ≫ productTransformation d =
      d.comparison.hom ≫ Functor.whiskerLeft d.tower (projectionNat U) := by
    apply derivedNatTrans_ext_on_KInjectives
    intro I hI
    let := hI
    exact projection_square_on_KInjective d T U I
  exact congr_app h M

private def canonicalDerivedUnit (G : A ⥤ B) [G.Additive]
    [Abelian.HasKInjectiveResolutions A] :
    G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ G.rightDerivedFunctor :=
  let π := HomotopyCategory.quotient A (.up ℤ)
  let H := G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let e : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ≅ π ⋙ H :=
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (G.mapHomotopyCategoryFactors (.up ℤ)).symm _ ≪≫
      Functor.associator _ _ _
  e.hom ≫ Functor.whiskerLeft π G.rightDerivedFunctorUnit ≫
    (Functor.associator _ _ _).inv ≫
    (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A)
      G.rightDerivedFunctor).hom

omit [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasLimitsOfShape ℕᵒᵖ B]
  [HasDerivedCategory (ℕᵒᵖ ⥤ B)] [HasCountableProducts A] [HasCountableProducts (DerivedCategory
  A)] [HasCountableProducts (DerivedCategory B)] [HasCountableProducts B] in
private theorem canonicalDerivedUnit_isIso (G : A ⥤ B) [G.Additive]
    [Abelian.HasKInjectiveResolutions A]
    (I : CochainComplex A ℤ) [I.IsKInjective] :
    IsIso ((canonicalDerivedUnit G).app I) := by
  dsimp [canonicalDerivedUnit]
  infer_instance

omit [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasLimitsOfShape ℕᵒᵖ B]
  [HasDerivedCategory (ℕᵒᵖ ⥤ B)] [HasCountableProducts A] [HasCountableProducts (DerivedCategory
  A)] [HasCountableProducts (DerivedCategory B)] [HasCountableProducts B] in
private theorem canonicalDerivedUnit_isRightDerived (G : A ⥤ B) [G.Additive]
    [Abelian.HasKInjectiveResolutions A] :
    G.rightDerivedFunctor.IsRightDerivedFunctor (canonicalDerivedUnit G)
      (HomologicalComplex.quasiIso A (.up ℤ)) := by
  let π := HomotopyCategory.quotient A (.up ℤ)
  let H := G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let e : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ≅ π ⋙ H :=
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (G.mapHomotopyCategoryFactors (.up ℤ)).symm _ ≪≫
      Functor.associator _ _ _
  have h : (CochainComplex.KInjectives.localizerMorphism A).Derives
      (G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) := by
    intro I J f hf
    have : IsIso (CochainComplex.KInjectives.toHomotopyCategory.map f) :=
      (CochainComplex.KInjectives.isIso_toHomotopyCategory_map_iff f).mpr hf
    have hmap := (HomotopyCategory.KInjectives.ι ⋙ H).map_isIso
      (CochainComplex.KInjectives.toHomotopyCategory.map f)
    have hmap' : IsIso ((π ⋙ H).map f.hom) := hmap
    have heq : (G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).map f.hom =
        e.hom.app I.obj ≫ (π ⋙ H).map f.hom ≫ e.inv.app J.obj := by
      rw [← e.hom.naturality_assoc]
      simp
    change IsIso ((G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).map f.hom)
    rw [heq]
    infer_instance
  exact h.isRightDerivedFunctor_of_isIso (canonicalDerivedUnit G) (fun I ↦ by
    have := I.property
    exact canonicalDerivedUnit_isIso G I.obj)

@[irreducible]
private def directIsoCanonical {G : A ⥤ B} [G.Additive]
    [Abelian.HasKInjectiveResolutions A] (d : DirectImageData G) :
    G.rightDerivedFunctor ≅ d.direct :=
  letI := d.direct_derived
  letI := canonicalDerivedUnit_isRightDerived G
  Functor.rightDerivedUnique G.rightDerivedFunctor d.direct
    (canonicalDerivedUnit G) d.unit (HomologicalComplex.quasiIso A (.up ℤ))

omit [HasCountableProducts A] [HasCountableProducts B] in
private theorem alpha_isIso {G : A ⥤ B} [G.Additive]
    [Abelian.HasKInjectiveResolutions A]
    (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (adj : F ⊣ G) (d : DirectImageData G)
    (M : DerivedCategory.{w} (ℕᵒᵖ ⥤ A)) : IsIso (alpha d M) := by
  let a := adj.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
    (directIsoCanonical d)
  let := a.isRightAdjoint
  dsimp [alpha]
  infer_instance

omit [HasCountableProducts A] [HasCountableProducts (DerivedCategory A)] [HasCountableProducts
  (DerivedCategory B)] [HasCountableProducts B] in
private theorem unit_shift {G : A ⥤ B} [G.Additive] (d : DirectImageData G)
    [d.direct.CommShift ℤ] [NatTrans.CommShift d.unit ℤ] (L : CochainComplex A ℤ) :
    d.unit.app (L⟦(1 : ℤ)⟧) ≫
        d.direct.map ((DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app L) ≫
        (d.direct.commShiftIso (1 : ℤ)).hom.app (DerivedCategory.Q.obj L) =
      DerivedCategory.Q.map
          (((G.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).hom.app L) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((G.mapHomologicalComplex (.up ℤ)).obj L) ≫
        (d.unit.app L)⟦(1 : ℤ)⟧' := by
  simpa only [Functor.commShiftIso_comp_hom_app, Category.assoc] using
    (NatTrans.shift_app_comm d.unit (1 : ℤ) L).symm

@[reassoc]
private theorem boundary_model {L : LimitData.{w} A} (T : RoosTriangleData L)
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (T.productComparison X).hom ≫ T.boundary (DerivedCategory.Q.obj X) =
      DerivedCategory.Q.map (roosBoundary.app X) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (roosF.obj X) ≫
          (T.coneComparison.hom.app X)⟦(1 : ℤ)⟧' :=
  T.boundary_model X

private theorem tower_grothendieck
    (C₀ : Type*) [Category C₀] [Abelian C₀] [IsGrothendieckAbelian.{g} C₀] :
    IsGrothendieckAbelian.{g} (ℕᵒᵖ ⥤ C₀) := by
  let G := separator C₀
  have hG := isSeparator_separator C₀
  have hS : ObjectProperty.IsSeparating
      (.ofObj fun j : ℕᵒᵖ ↦ (evaluationLeftAdjoint C₀ j).obj G) := by
    intro F F' f k hfk
    apply NatTrans.ext
    funext j
    apply hG.def
    intro a
    let adj := evaluationAdjunctionRight C₀ j
    apply (adj.homEquiv G F').symm.injective
    have h := hfk _ (ObjectProperty.ofObj_apply _ j) ((adj.homEquiv G F).symm a)
    exact (adj.homEquiv_naturality_right_symm a f).trans
      (h.trans (adj.homEquiv_naturality_right_symm a k).symm)
  let : HasSeparator (ℕᵒᵖ ⥤ C₀) := ⟨_, hS.isSeparator_coproduct⟩
  let : HasFilteredColimitsOfSize.{g, g} (ℕᵒᵖ ⥤ C₀) := ⟨fun _ _ _ ↦ inferInstance⟩
  let : AB5OfSize.{g, g} (ℕᵒᵖ ⥤ C₀) := ⟨fun _ _ _ ↦ inferInstance⟩
  exact { locallySmall := ⟨fun P Q ↦ small_of_injective
    (f := fun f : P ⟶ Q ↦ f.app) (fun f k h ↦ NatTrans.ext h)⟩ }

end PrivateSquares

end DirectImageRoosNormalization

open DirectImageRoosNormalization

end CategoryTheory
