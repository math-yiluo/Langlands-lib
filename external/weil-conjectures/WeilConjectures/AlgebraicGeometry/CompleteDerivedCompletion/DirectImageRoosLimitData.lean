/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.CompleteDerivedCompletion
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.CategoryTheory.DirectImageRoosNormalization.DirectImageRoosNormalization
import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.RingTheory.ProEtale.WContractible
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.CategoryTheory.Ringed.RingedConstantTowerPushforwardNormalization
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitTowerTriangle
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement

/-!
# Roos limit data for complete direct images

This is the Milnor cone and product-comparison part of the direct-image limits
proposition.  It is split from the final assembly because it requires the full
normalized Roos calculation.

Source: literature/blueprint/latest/blueprint/sec-proper-base-change/
sk-prop-pbc-complete/prop-weil-pbc-direct-image-limits.proof.md, proof (1).
(blueprint: prop-weil-pbc-direct-image-limits-roos-data)
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.CompleteDerivedCompletion

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.modulesDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The constant tower evaluated at a level is canonically the identity.
Source: assertion (1), Milnor-cone projections.
(blueprint: prop-weil-pbc-direct-image-limits-roos-data) -/
def constantEvaluationIso (T : Scheme.{u}) (n : ℕ) :
    dconstant l E T ⋙ dev l E T n ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryCompIso (constant l E T) (ev l E T n) ≪≫
    Functor.mapDerivedCategoryNatIso
      (Functor.constCompEvaluationObj (C := ℕᵒᵖ) (D := AdicCompletion.Modules l E T)
        (Opposite.op n)) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- Canonical projection from a derived limit to one tower level.
Source: assertion (1), Milnor-cone projections.
(blueprint: prop-weil-pbc-direct-image-limits-roos-data) -/
def levelProjection (T : Scheme.{u}) (n : ℕ) : rlim l E T ⟶ dev l E T n :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft (rlim l E T) (constantEvaluationIso l E T n).inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (constantLimitAdjunction l E T).counit (dev l E T n) ≫
    (Functor.leftUnitor _).hom

section RoosTriangle

attribute [local instance] AdicCompletion.modulesProducts

set_option backward.isDefEq.respectTransparency false in
private theorem factorsh_hom' {B D : Type*} [Category B] [Category D]
    [Abelian B] [Abelian D] [HasDerivedCategory B] [HasDerivedCategory D]
    (F : B ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (J : CochainComplex B ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj J) =
      F.mapDerivedCategoryFactors.hom.app J := by
  have h1 : (DerivedCategory.quotientCompQhIso B).hom.app J = 𝟙 _ := rfl
  have h2 : (DerivedCategory.quotientCompQhIso D).inv.app
      ((F.mapHomologicalComplex _).obj J) = 𝟙 _ := rfl
  have h3 : (F.mapHomotopyCategoryFactors (.up ℤ)).inv.app J = 𝟙 _ := rfl
  simp only [Functor.mapDerivedCategoryFactorsh_hom_app, h1, h2, h3,
    CategoryTheory.Functor.map_id, Category.id_comp]
  erw [DerivedCategory.Qh.map_id, Category.comp_id, Category.comp_id]

private theorem constantEvaluation_factors (T : Scheme.{u}) (n : ℕ)
    (J : CochainComplex (AdicCompletion.Modules l E T) ℤ) :
    (constantEvaluationIso l E T n).hom.app (DerivedCategory.Q.obj J) =
      (dev l E T n).map ((constant l E T).mapDerivedCategoryFactors.hom.app J) ≫
      (ev l E T n).mapDerivedCategoryFactors.hom.app
        (((constant l E T).mapHomologicalComplex (.up ℤ)).obj J) := by
  let D := constant l E T
  let F := ev l E T n
  change (Functor.mapDerivedCategoryCompIso D F).hom.app (DerivedCategory.Q.obj J) ≫
    (Functor.mapDerivedCategoryNatIso (Iso.refl _)).hom.app (DerivedCategory.Q.obj J) ≫
      (Functor.mapDerivedCategoryIdIso _).hom.app (DerivedCategory.Q.obj J) = _
  rw [Functor.mapDerivedCategoryNatIso_refl]
  simp only [NatTrans.id_app]
  have hi := Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj (AdicCompletion.Modules l E T)
    ((HomotopyCategory.quotient _ (.up ℤ)).obj J)
  change (Functor.mapDerivedCategoryIdIso _).hom.app (DerivedCategory.Q.obj J) =
    (𝟭 _).mapDerivedCategoryFactorsh.hom.app _ at hi
  rw [hi]
  erw [factorsh_hom']
  have h := Functor.mapDerivedCategoryCompIso_hom_app_factors D F J
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso D F).inv.app
    (DerivedCategory.Q.obj J))).mp
  simp only [Iso.inv_hom_id_app_assoc]
  erw [Category.id_comp]
  exact h.symm

private theorem derivedCounit_unit
    {B C : Type*} [Category B] [Category C] [Abelian B] [Abelian C]
    [HasDerivedCategory B] [HasDerivedCategory C]
    [Abelian.HasKInjectiveResolutions C]
    {L : B ⥤ C} {R : C ⥤ B} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (adj : L ⊣ R) (J : CochainComplex C ℤ) :
    L.mapDerivedCategory.map
        (R.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj J)) ≫
      adj.mapDerivedCategoryRightDerivedAdjunction.counit.app (DerivedCategory.Q.obj J) =
    L.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj J) ≫
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).counit.app J) := by
  have h := (adj.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso C (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    R.rightDerivedFunctorUnit ((HomotopyCategory.quotient _ _).obj J)
  erw [factorsh_hom' L ((R.mapHomologicalComplex (.up ℤ)).obj J)] at h
  rw [Adjunction.mapHomotopyCategory_counit_app_quotient] at h
  exact h

theorem levelProjection_app (T : Scheme.{u}) (n : ℕ) (M : DTow l E T) :
    (levelProjection l E T n).app M =
      (constantEvaluationIso l E T n).inv.app ((rlim l E T).obj M) ≫
        (dev l E T n).map ((constantLimitAdjunction l E T).counit.app M) := by
  simp [levelProjection]

private theorem levelProjection_unit (T : Scheme.{u}) (n : ℕ)
    (J : CochainComplex (Tow l E T) ℤ) :
    (inverseLimit l E T).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj J) ≫
      (levelProjection l E T n).app (DerivedCategory.Q.obj J) =
    DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex (lim.π (Opposite.op n) :
        (inverseLimit l E T) ⟶ ev l E T n) (.up ℤ)).app J) ≫
      (ev l E T n).mapDerivedCategoryFactors.inv.app J := by
  let Ev := ev l E T n
  let C := constant l E T
  let L := inverseLimit l E T
  let e := constantEvaluationIso l E T n
  let unit := L.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj J)
  have hc := derivedCounit_unit (constLimAdj : C ⊣ L) J
  have hn := e.inv.naturality unit
  change unit ≫ e.inv.app _ = e.inv.app _ ≫ Ev.mapDerivedCategory.map
    (C.mapDerivedCategory.map unit) at hn
  rw [levelProjection_app]
  change unit ≫ (e.inv.app _ ≫ Ev.mapDerivedCategory.map _) = _
  rw [← Category.assoc, hn, Category.assoc, ← Ev.mapDerivedCategory.map_comp]
  erw [hc]
  rw [Ev.mapDerivedCategory.map_comp]
  rw [← Category.assoc]
  have hf := constantEvaluation_factors l E T n ((L.mapHomologicalComplex (.up ℤ)).obj J)
  have he : e.inv.app _ ≫ Ev.mapDerivedCategory.map
      (C.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj J)) =
    Ev.mapDerivedCategoryFactors.inv.app
      ((C.mapHomologicalComplex (.up ℤ)).obj ((L.mapHomologicalComplex (.up ℤ)).obj J)) := by
    apply (cancel_mono (Ev.mapDerivedCategoryFactors.hom.app _)).mp
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [← hf]
    exact e.inv_hom_id_app _
  erw [he]
  exact (Ev.mapDerivedCategoryFactors.inv.naturality
    (((constLimAdj : C ⊣ L).mapHomologicalComplex (.up ℤ)).counit.app J)).symm

private theorem transition_fac (T : Scheme.{u}) (n : ℕ) (J : CochainComplex (Tow l E T) ℤ) :
    (transition l E T n).app (DerivedCategory.Q.obj J) ≫
        (ev l E T n).mapDerivedCategoryFactors.hom.app J =
      (ev l E T (n + 1)).mapDerivedCategoryFactors.hom.app J ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          ((evaluation ℕᵒᵖ (AdicCompletion.Modules l E T)).map
            (homOfLE (Nat.le_succ n)).op) (.up ℤ)).app J) := by
  have hm : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso (Tow l E T) (.up ℤ))
      ((ev l E T (n + 1)).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      (ev l E T (n + 1)).mapDerivedCategory =
        (ev l E T (n + 1)).mapDerivedCategoryFactors := rfl
  have hn : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso (Tow l E T) (.up ℤ))
      ((ev l E T n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      (ev l E T n).mapDerivedCategory =
        (ev l E T n).mapDerivedCategoryFactors := rfl
  simp [transition, towerDerivedEvaluationTransition, Localization.liftNatTrans_app, hm, hn]

/-- The Milnor (Roos) triangle of a derived tower, with the level projections as first map.
Source: Stacks Tags 0941 and 08TC; proof (1) of proposition-proper-base-change-complete-integral--1.
Proof: represent `M` by a K-injective tower complex `J`. The ordinary limit cone of `J`
gives a distinguished Roos triangle in the derived category, by exactness of countable
products of pro-étale module sheaves. The invertible derived unit identifies its first
object with `rlim M`, and the evaluation factorizations identify its other objects with
the levels of `M`; the limit projections become the level projections, and the strict
transitions become the derived transitions. Transport the triangle along these
isomorphisms. (blueprint: proposition-proper-base-change-complete-integral--1) -/
theorem roos_triangle (T : Scheme.{u})
    [HasCountableProducts (DerivedCategory (AdicCompletion.Modules l E T))] (M : DTow l E T) :
    ∃ δ, IsDerivedLimitTriangle (fun n : ℕ ↦ (transition l E T n).app M) _
      (Pi.lift fun n : ℕ ↦ (levelProjection l E T n).app M) δ := by
  have : CountableAB4Star (AdicCompletion.Modules l E T) :=
    AdicCompletion.modules_countableAB4Star l E T
  obtain ⟨J, hJ, ⟨eM⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective M
  let c : Cone J.asFunctor :=
    { pt := ((inverseLimit l E T).mapHomologicalComplex (.up ℤ)).obj J
      π :=
        { app := fun n ↦ (NatTrans.mapHomologicalComplex (lim.π n) (.up ℤ)).app J
          naturality := by
            intro n m g
            apply HomologicalComplex.Hom.ext
            funext i
            exact (limit.w (J.X i) g).symm } }
  have hc : IsLimit c := by
    apply HomologicalComplex.isLimitOfEval
    intro i
    exact limit.isLimit (J.X i)
  obtain ⟨δ, hδ⟩ := derivedCategory_towerLimit_triangle (AdicCompletion.Modules l E T)
    inferInstance inferInstance J c hc
  let en (n : ℕ) : DerivedCategory.Q.obj (J.asFunctor.obj (Opposite.op n)) ≅
      (dev l E T n).obj M :=
    ((ev l E T n).mapDerivedCategoryFactors.app J).symm ≪≫ (dev l E T n).mapIso eM.symm
  let eL : DerivedCategory.Q.obj c.pt ≅ (rlim l E T).obj M :=
    asIso ((inverseLimit l E T).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj J)) ≪≫ (rlim l E T).mapIso eM.symm
  let ep := Pi.mapIso en
  have hp : eL.hom ≫ Pi.lift (fun n : ℕ ↦ (levelProjection l E T n).app M) =
      Pi.lift (fun n : ℕ ↦ DerivedCategory.Q.map (c.π.app (Opposite.op n))) ≫ ep.hom := by
    apply Pi.hom_ext
    intro n
    simp only [ep, Category.assoc, Pi.lift_comp_π, Pi.mapIso_hom_π, Pi.lift_comp_π_assoc]
    dsimp only [eL, en, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_hom,
      Iso.app_inv]
    erw [Category.assoc, (levelProjection l E T n).naturality]
    erw [← Category.assoc, levelProjection_unit]
    simp only [Category.assoc]
    rfl
  have hn (n : ℕ) : (en (n + 1)).hom ≫ (transition l E T n).app M =
      DerivedCategory.Q.map (J.asFunctor.map (homOfLE (Nat.le_succ n)).op) ≫
        (en n).hom := by
    dsimp only [en, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_inv]
    rw [Category.assoc, (transition l E T n).naturality, ← Category.assoc,
      ← Category.assoc]
    congr 1
    apply (cancel_mono ((ev l E T n).mapDerivedCategoryFactors.hom.app J)).mp
    simp only [Category.assoc, transition_fac, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    rfl
  have ht : ep.hom ≫ towerTransitionEndomorphism (fun n : ℕ ↦ (transition l E T n).app M) =
      towerTransitionEndomorphism (fun n : ℕ ↦ DerivedCategory.Q.map
        (J.asFunctor.map (homOfLE (Nat.le_succ n)).op)) ≫ ep.hom :=
    towerTransitionEndomorphism_natural_backward _ _ (fun n ↦ (en n).hom) hn
  refine ⟨ep.inv ≫ δ ≫ (shiftFunctor _ (1 : ℤ)).map eL.hom, ?_⟩
  exact (Pretriangulated.distinguished_iff_of_iso
    (Pretriangulated.Triangle.isoMk _ _ eL ep ep hp.symm ht.symm (by simp))).mp hδ

end RoosTriangle

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

section ProjectionSquare

set_option backward.isDefEq.respectTransparency false in
private theorem towerInterchange_fac'
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
    (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (n : ℕᵒᵖ) (K : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) :
    (towerDerivedEvaluationInterchange F n).hom.app (DerivedCategory.Q.obj K) ≫
        F.mapDerivedCategory.map
          (((evaluation ℕᵒᵖ B).obj n).mapDerivedCategoryFactors.hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app
          ((((evaluation ℕᵒᵖ B).obj n).mapHomologicalComplex (.up ℤ)).obj K) =
      ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory.map
          (((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapDerivedCategoryFactors.hom.app K) ≫
        ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors.hom.app
          ((((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapHomologicalComplex (.up ℤ)).obj K) := by
  let FT := (Functor.whiskeringRight ℕᵒᵖ B A).obj F
  let EA := (evaluation ℕᵒᵖ A).obj n
  let EB := (evaluation ℕᵒᵖ B).obj n
  apply (cancel_epi
    ((Functor.mapDerivedCategoryCompIso FT EA).inv.app (DerivedCategory.Q.obj K))).mp
  dsimp only [FT, EA, EB]
  simp only [towerDerivedEvaluationInterchange, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app_assoc]
  exact (Functor.mapDerivedCategoryCompIso_hom_app_factors EB F K).trans
    (Functor.mapDerivedCategoryCompIso_hom_app_factors FT EA K).symm

private theorem pullEvaluation_fac (n : ℕ) (K : CochainComplex (Tow l E Y) ℤ) :
    (pullEvaluation l E f n).hom.app (DerivedCategory.Q.obj K) ≫
        (dpullModule l E f).map ((ev l E Y n).mapDerivedCategoryFactors.hom.app K) ≫
        (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f
          ).mapDerivedCategoryFactors.hom.app
          (((ev l E Y n).mapHomologicalComplex (.up ℤ)).obj K) =
      (dev l E X n).map ((pull l E f).mapDerivedCategoryFactors.hom.app K) ≫
        (ev l E X n).mapDerivedCategoryFactors.hom.app
          (((pull l E f).mapHomologicalComplex (.up ℤ)).obj K) :=
  towerInterchange_fac' _ _ K

set_option backward.isDefEq.respectTransparency false in
private theorem constantInterchange_fac (J : CochainComplex (AdicCompletion.Modules l E Y) ℤ) :
    (constantInterchange l E (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f)
        ).hom.app (DerivedCategory.Q.obj J) ≫
      (dpull l E f).map ((constant l E Y).mapDerivedCategoryFactors.hom.app J) ≫
      (pull l E f).mapDerivedCategoryFactors.hom.app
        (((constant l E Y).mapHomologicalComplex (.up ℤ)).obj J) =
    (dconstant l E X).map ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) f
        ).mapDerivedCategoryFactors.hom.app J) ≫
      (constant l E X).mapDerivedCategoryFactors.hom.app
        (((CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).mapHomologicalComplex
          (.up ℤ)).obj J) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (Functor.compConstIso ℕᵒᵖ
        (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f)).hom (.up ℤ)).app J) := by
  let U := CondensedRing.upperStar (DerivedNakayama.integerRing l E) f
  have h1 := Functor.mapDerivedCategoryCompIso_hom_app_factors (constant l E Y) (pull l E f) J
  have h2 := Functor.mapDerivedCategoryCompIso_hom_app_factors U (constant l E X) J
  have h3 : (Functor.mapDerivedCategoryNatIso (Functor.compConstIso ℕᵒᵖ U)).hom.app
      (DerivedCategory.Q.obj J) ≫
      (constant l E Y ⋙ pull l E f).mapDerivedCategoryFactors.hom.app J =
      (U ⋙ constant l E X).mapDerivedCategoryFactors.hom.app J ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (Functor.compConstIso ℕᵒᵖ U).hom (.up ℤ)).app J) :=
    Functor.mapDerivedCategoryNatIso_fac _ J
  simp only [constantInterchange, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc]
  have e1 := congrArg (fun x ↦ (Functor.mapDerivedCategoryCompIso U (constant l E X)).hom.app
    (DerivedCategory.Q.obj J) ≫ (Functor.mapDerivedCategoryNatIso
      (Functor.compConstIso ℕᵒᵖ U)).hom.app (DerivedCategory.Q.obj J) ≫ x) h1
  have e2 := congrArg (fun x ↦ (Functor.mapDerivedCategoryCompIso U (constant l E X)).hom.app
    (DerivedCategory.Q.obj J) ≫ x) h3
  have e3 : (Functor.mapDerivedCategoryCompIso U (constant l E X)).hom.app
      (DerivedCategory.Q.obj J) ≫ (U ⋙ constant l E X).mapDerivedCategoryFactors.hom.app J =
      (constant l E X).mapDerivedCategory.map (U.mapDerivedCategoryFactors.hom.app J) ≫
        (constant l E X).mapDerivedCategoryFactors.hom.app
          ((U.mapHomologicalComplex (.up ℤ)).obj J) := by
    rw [← h2, Iso.hom_inv_id_app_assoc]
  exact (e1.trans e2).trans ((reassoc_of% e3) _)

set_option backward.isDefEq.respectTransparency false in
private theorem constant_coherence_Q (n : ℕ)
    (J : CochainComplex (AdicCompletion.Modules l E Y) ℤ) :
    (dpullModule l E f).map
        ((constantEvaluationIso l E Y n).inv.app (DerivedCategory.Q.obj J)) ≫
      (pullEvaluation l E f n).inv.app ((dconstant l E Y).obj (DerivedCategory.Q.obj J)) =
    (constantEvaluationIso l E X n).inv.app
        ((dpullModule l E f).obj (DerivedCategory.Q.obj J)) ≫
      (dev l E X n).map ((constantInterchange l E
        (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f)).hom.app
          (DerivedCategory.Q.obj J)) := by
  let U := CondensedRing.upperStar (DerivedNakayama.integerRing l E) f
  let CJ := ((constant l E Y).mapHomologicalComplex (.up ℤ)).obj J
  let g := (constant l E Y).mapDerivedCategoryFactors.hom.app J
  apply (cancel_mono ((dev l E X n).map ((dpull l E f).map g) ≫
    (dev l E X n).map ((pull l E f).mapDerivedCategoryFactors.hom.app CJ) ≫
    (ev l E X n).mapDerivedCategoryFactors.hom.app
      (((pull l E f).mapHomologicalComplex (.up ℤ)).obj CJ))).mp
  have hY := constantEvaluation_factors l E Y n J
  have hX := constantEvaluation_factors l E X n ((U.mapHomologicalComplex (.up ℤ)).obj J)
  have hP := pullEvaluation_fac l E f n CJ
  have hC := constantInterchange_fac l E f J
  have hPinv : (pullEvaluation l E f n).inv.app (DerivedCategory.Q.obj CJ) ≫
      (dev l E X n).map ((pull l E f).mapDerivedCategoryFactors.hom.app CJ) ≫
      (ev l E X n).mapDerivedCategoryFactors.hom.app
        (((pull l E f).mapHomologicalComplex (.up ℤ)).obj CJ) =
      (dpullModule l E f).map ((ev l E Y n).mapDerivedCategoryFactors.hom.app CJ) ≫
      U.mapDerivedCategoryFactors.hom.app
        (((ev l E Y n).mapHomologicalComplex (.up ℤ)).obj CJ) := by
    rw [← hP, Iso.inv_hom_id_app_assoc]
  have hnat : (pullEvaluation l E f n).inv.app ((dconstant l E Y).obj (DerivedCategory.Q.obj J))
      ≫ (dev l E X n).map ((dpull l E f).map g) =
      (dpullModule l E f).map ((dev l E Y n).map g) ≫
        (pullEvaluation l E f n).inv.app (DerivedCategory.Q.obj CJ) :=
    ((pullEvaluation l E f n).inv.naturality g).symm
  have hnatX : U.mapDerivedCategoryFactors.hom.app J ≫
      (constantEvaluationIso l E X n).inv.app
        (DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj J)) =
      (constantEvaluationIso l E X n).inv.app ((dpullModule l E f).obj (DerivedCategory.Q.obj J))
        ≫ (dev l E X n).map ((dconstant l E X).map (U.mapDerivedCategoryFactors.hom.app J)) :=
    (constantEvaluationIso l E X n).inv.naturality _
  have hYi : (constantEvaluationIso l E Y n).inv.app (DerivedCategory.Q.obj J) ≫
      (dev l E Y n).map g ≫ (ev l E Y n).mapDerivedCategoryFactors.hom.app CJ = 𝟙 _ := by
    rw [← hY, Iso.inv_hom_id_app]
  have hXi : (constantEvaluationIso l E X n).inv.app
        (DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj J)) ≫
      (dev l E X n).map ((constant l E X).mapDerivedCategoryFactors.hom.app
        ((U.mapHomologicalComplex (.up ℤ)).obj J)) =
      (ev l E X n).mapDerivedCategoryFactors.inv.app
        (((constant l E X).mapHomologicalComplex (.up ℤ)).obj
          ((U.mapHomologicalComplex (.up ℤ)).obj J)) := by
    rw [← cancel_mono ((ev l E X n).mapDerivedCategoryFactors.hom.app _), Category.assoc,
      ← hX, Iso.inv_hom_id_app, Iso.inv_hom_id_app]
    rfl
  have hev := (ev l E X n).mapDerivedCategoryFactors.hom.naturality
    ((NatTrans.mapHomologicalComplex (Functor.compConstIso ℕᵒᵖ U).hom (.up ℤ)).app J)
  have he : ((ev l E X n).mapHomologicalComplex (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex (Functor.compConstIso ℕᵒᵖ U).hom (.up ℤ)).app J) =
      𝟙 _ := by
    ext i : 1
    rfl
  have hL : (dpullModule l E f).map ((constantEvaluationIso l E Y n).inv.app
      (DerivedCategory.Q.obj J)) ≫ (dpullModule l E f).map ((dev l E Y n).map g) ≫
      (dpullModule l E f).map ((ev l E Y n).mapDerivedCategoryFactors.hom.app CJ) = 𝟙 _ := by
    rw [← Functor.map_comp, ← Functor.map_comp, hYi, CategoryTheory.Functor.map_id]
  have hLHS : ((dpullModule l E f).map
        ((constantEvaluationIso l E Y n).inv.app (DerivedCategory.Q.obj J)) ≫
      (pullEvaluation l E f n).inv.app ((dconstant l E Y).obj (DerivedCategory.Q.obj J))) ≫
      (dev l E X n).map ((dpull l E f).map g) ≫
      (dev l E X n).map ((pull l E f).mapDerivedCategoryFactors.hom.app CJ) ≫
      (ev l E X n).mapDerivedCategoryFactors.hom.app
        (((pull l E f).mapHomologicalComplex (.up ℤ)).obj CJ) =
      U.mapDerivedCategoryFactors.hom.app J := by
    rw [Category.assoc, reassoc_of% hnat, hPinv]
    exact (reassoc_of% hL) _
  have hRHS : ((constantEvaluationIso l E X n).inv.app
        ((dpullModule l E f).obj (DerivedCategory.Q.obj J)) ≫
      (dev l E X n).map ((constantInterchange l E U).hom.app (DerivedCategory.Q.obj J))) ≫
      (dev l E X n).map ((dpull l E f).map g) ≫
      (dev l E X n).map ((pull l E f).mapDerivedCategoryFactors.hom.app CJ) ≫
      (ev l E X n).mapDerivedCategoryFactors.hom.app
        (((pull l E f).mapHomologicalComplex (.up ℤ)).obj CJ) =
      U.mapDerivedCategoryFactors.hom.app J := by
    let eX := (constantEvaluationIso l E X n).inv
    let D := dev l E X n
    let Uf := U.mapDerivedCategoryFactors.hom.app J
    let UJ := (U.mapHomologicalComplex (.up ℤ)).obj J
    let Cf := (constant l E X).mapDerivedCategoryFactors.hom.app UJ
    let Qe := DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
      (Functor.compConstIso ℕᵒᵖ U).hom (.up ℤ)).app J)
    let Df := (ev l E X n).mapDerivedCategoryFactors.hom.app
      (((pull l E f).mapHomologicalComplex (.up ℤ)).obj CJ)
    calc _ = eX.app ((dpullModule l E f).obj (DerivedCategory.Q.obj J)) ≫
          D.map ((dconstant l E X).map Uf) ≫ D.map Cf ≫ D.map Qe ≫ Df := by
          have h := congrArg (fun x ↦ eX.app ((dpullModule l E f).obj
            (DerivedCategory.Q.obj J)) ≫ D.map x ≫ Df) hC
          simpa only [Category.assoc, Functor.map_comp] using h
      _ = Uf ≫ eX.app (DerivedCategory.Q.obj UJ) ≫ D.map Cf ≫ D.map Qe ≫ Df := by
          have h := hnatX =≫ (D.map Cf ≫ D.map Qe ≫ Df)
          simpa only [Category.assoc] using h.symm
      _ = Uf ≫ (ev l E X n).mapDerivedCategoryFactors.inv.app
            (((constant l E X).mapHomologicalComplex (.up ℤ)).obj UJ) ≫ D.map Qe ≫ Df := by
          have h := Uf ≫= (hXi =≫ (D.map Qe ≫ Df))
          simpa only [Category.assoc] using h
      _ = Uf ≫ DerivedCategory.Q.map (((ev l E X n).mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex (Functor.compConstIso ℕᵒᵖ U).hom (.up ℤ)).app J)) := by
          congr 1
          rw [← cancel_epi ((ev l E X n).mapDerivedCategoryFactors.hom.app
            (((constant l E X).mapHomologicalComplex (.up ℤ)).obj UJ)),
            Iso.hom_inv_id_app_assoc]
          exact hev
      _ = Uf := by
          rw [he]
          exact (congrArg (Uf ≫ ·) (DerivedCategory.Q.map_id _)).trans (Category.comp_id _)
  exact hLHS.trans hRHS.symm
end ProjectionSquare

/-- Roos triangles, product comparison and the projection compatibility for direct image,
with the levelwise evaluation isomorphisms: assertion (1) of
proposition-proper-base-change-complete-integral--1, with its Milnor-cone description.
Source: literature/blueprint/latest/blueprint/sec-proper-base-change/sk-prop-pbc-complete/
prop-weil-pbc-direct-image-limits.proof.md, proof (1); Stacks Tag 0A07.
(blueprint: prop-weil-pbc-direct-image-limits-roos-data)

Proof. The tower direct image is the derived functor of `f_*` applied levelwise, so by
assertions (3) and (4) of proposition-proper-base-change-complete-integral its evaluation at level
`n` is canonically `Rf_*` of the evaluation at `n`: this is `pushEvaluationMap`, invertible
for every `n`. Products of sheaves of modules on the pro-étale site are exact
(proposition-exact-products--1), so both derived categories have countable products, computed
termwise. For a tower `M` the derived limit `rlim M` is the right adjoint of the constant
tower, and its counit at level `n` is `levelProjection`; by def-weil-derived-limit the
derived limit sits in the Milnor (Roos) triangle
`rlim M → ∏ M_n --(1-T)--> ∏ M_n → rlim M[1]` whose first map has components the level
projections. This holds on `X` for `M` and on `Y` for `Rf_*^Tow M`. The product
comparison `Rf_* ∏ M_n → ∏ Rf_* M_n` is invertible because `Rf_*` is a right adjoint, and
it commutes with `1-T` because `T` is a product of transition maps and the comparison is
natural in each factor. Finally `pushLimitIso` is the conjugate of the constant/pullback
comparison, so it is compatible with the counits of the two constant-limit adjunctions;
composing with `pushEvaluationMap` gives the level-projection square. The normalized
direct-image Roos comparison lem-weil-pbc-direct-image-roos-normalization packages the
product, `1-T` and connecting-morphism squares. -/
theorem directImage_roos_limit_data :
    (∀ n : ℕ, IsIso (pushEvaluationMap l E f n)) ∧
    (∃ (_ : HasCountableProducts (DerivedCategory (AdicCompletion.Modules l E X)))
      (_ : HasCountableProducts (DerivedCategory (AdicCompletion.Modules l E Y))),
      ∀ M : DTow l E X,
        (∃ δ, IsDerivedLimitTriangle (fun n : ℕ ↦ (transition l E X n).app M) _
          (Pi.lift fun n : ℕ ↦ (levelProjection l E X n).app M) δ) ∧
        (∃ δ, IsDerivedLimitTriangle
          (fun n : ℕ ↦ (transition l E Y n).app ((rpush l E f).obj M)) _
          (Pi.lift fun n : ℕ ↦ (levelProjection l E Y n).app ((rpush l E f).obj M)) δ) ∧
        IsIso (piComparison (rpushModule l E f) (fun n : ℕ ↦ (dev l E X n).obj M)) ∧
        (rpushModule l E f).map
            (towerTransitionEndomorphism (fun n : ℕ ↦ (transition l E X n).app M)) ≫
            piComparison (rpushModule l E f) (fun n : ℕ ↦ (dev l E X n).obj M) =
          piComparison (rpushModule l E f) (fun n : ℕ ↦ (dev l E X n).obj M) ≫
            towerTransitionEndomorphism
              (fun n : ℕ ↦ (rpushModule l E f).map ((transition l E X n).app M)) ∧
        ∀ n : ℕ, (pushLimitIso l E f).hom.app M ≫
            (levelProjection l E Y n).app ((rpush l E f).obj M) ≫
            (pushEvaluationMap l E f n).app M =
          (rpushModule l E f).map ((levelProjection l E X n).app M)) := by
  sorry

end AlgebraicGeometry.ProEtale.CompleteDerivedCompletion
