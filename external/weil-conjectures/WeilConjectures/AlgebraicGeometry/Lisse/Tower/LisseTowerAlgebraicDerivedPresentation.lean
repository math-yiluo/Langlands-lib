/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantRealizationDataSupplement
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerLocalAlgebraicReductionDiagram
import WeilConjectures.RingTheory.AdicCompletionNoetherianOfQuotient
import WeilConjectures.RingTheory.DerivedModuleScalarAdjunction
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.ProperBaseChange.PseudoCoherentNormalizedAlgebraTowerSupplement
import WeilConjectures.CategoryTheory.Finite.FiniteMittagLeffler
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsExistence
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import WeilConjectures.CategoryTheory.DerivedLimitRoosAbelianGroups
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Completeness

/-! # Algebraic derived presentations of lisse towers

## References

* Stacks Project, Pro-etale Cohomology, Tag 09BV
* More on Algebra, Tag 09AV
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w r u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem map_roos {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive]
    (K : ℕ → C) [HasProduct K] [HasProduct (fun n ↦ F.obj (K n))]
    (f : ∀ n, K (n + 1) ⟶ K n) :
    F.map (towerTransitionEndomorphism f) ≫ piComparison F K =
      piComparison F K ≫ towerTransitionEndomorphism (fun n ↦ F.map (f n)) := by
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, piComparison_comp_π, towerTransitionEndomorphism,
    towerProductShift, Preadditive.sub_comp, Category.id_comp, Pi.lift_comp_π,
    Preadditive.comp_sub, ← F.map_comp, F.map_sub]
  congr 1
  rw [← Category.assoc, piComparison_comp_π]
  exact F.map_comp _ _

private theorem module_roos_epi {R : Type r} [CommRing R]
    (K : ℕᵒᵖ ⥤ ModuleCat.{r} R) (hfinite : ∀ n, Finite (K.obj n)) :
    Epi (towerTransitionEndomorphism (K := fun n ↦ K.obj (op n))
      (fun n ↦ K.map (homOfLE (Nat.le_succ n)).op)) := by
  let F := forget₂ (ModuleCat.{r} R) AddCommGrpCat.{r}
  let B := K ⋙ F
  obtain ⟨_, e, _⟩ := derivedLimitRoosAbelianGroups.2
  have hz : IsZero (cokernel (roosMap B)) :=
    ((finiteTower_mittagLeffler_vanishing B hfinite).2).of_iso (e B).symm
  have : Epi (roosMap B) := Preadditive.epi_of_isZero_cokernel _ hz
  let t := towerTransitionEndomorphism (K := fun n ↦ K.obj (op n))
    (fun n ↦ K.map (homOfLE (Nat.le_succ n)).op)
  let c := PreservesProduct.iso F (fun n ↦ K.obj (op n))
  have he : F.map t = c.hom ≫ roosMap B ≫ c.inv := by
    apply (cancel_mono c.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact map_roos F _ _
  have : Epi (F.map t) := by rw [he]; infer_instance
  exact (ModuleCat.epi_iff_surjective _).2
    ((AddCommGrpCat.epi_iff_surjective (F.map t)).1 inferInstance)

private theorem module_derivedLimit_interval {R : Type r} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{r} R)]
    (K : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{r} R))
    [HasProduct (fun n : ℕ ↦ K.obj (op n))]
    (L : DerivedCategory (ModuleCat.{r} R))
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj (op n))
    (δ : (∏ᶜ fun n : ℕ ↦ K.obj (op n)) ⟶ L⟦(1 : ℤ)⟧)
    (hT : IsDerivedLimitTriangle (fun n ↦ K.map (homOfLE (Nat.le_succ n)).op) L p δ)
    (a b : ℤ)
    (hfinite : ∀ (n : ℕᵒᵖ) (i : ℤ),
      Finite ((DerivedCategory.homologyFunctor (ModuleCat.{r} R) i).obj (K.obj n)))
    (hbounded : ∀ (n : ℕᵒᵖ) (i : ℤ), (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{r} R) i).obj (K.obj n))) :
    ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{r} R) i).obj L) := by
  obtain ⟨hP, _, hH⟩ := derivedCategory_countableProducts_core (ModuleCat.{r} R)
  let _ := hP
  intro i hi
  let H := DerivedCategory.homologyFunctor (ModuleCat.{r} R) (i - 1)
  have := hH ℕ (i - 1)
  have := hH ℕ i
  let t := towerTransitionEndomorphism (K := fun n ↦ K.obj (op n))
    (fun n ↦ K.map (homOfLE (Nat.le_succ n)).op)
  have hep : Epi (towerTransitionEndomorphism (K := fun n ↦ H.obj (K.obj (op n)))
      (fun n ↦ H.map (K.map (homOfLE (Nat.le_succ n)).op))) :=
    module_roos_epi (K ⋙ H) (fun n ↦ hfinite n (i - 1))
  let c := PreservesProduct.iso H (fun n ↦ K.obj (op n))
  have he : H.map t = c.hom ≫
      towerTransitionEndomorphism (K := fun n ↦ H.obj (K.obj (op n)))
        (fun n ↦ H.map (K.map (homOfLE (Nat.le_succ n)).op)) ≫
        c.inv := by
    apply (cancel_mono c.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact map_roos H _ _
  have : Epi (H.map t) := by rw [he]; infer_instance
  let T := Pretriangulated.Triangle.mk p t δ
  have hepT : Epi (H.map T.mor₂) := by
    change Epi (H.map t)
    infer_instance
  have hzδ : DerivedCategory.HomologySequence.δ T (i - 1) i = 0 :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT (i - 1) i).1
      inferInstance
  have : Mono ((DerivedCategory.homologyFunctor (ModuleCat.{r} R) i).map p) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (i - 1) i).2 hzδ
  have hz : IsZero (∏ᶜ fun n : ℕ ↦
      (DerivedCategory.homologyFunctor (ModuleCat.{r} R) i).obj (K.obj (op n))) :=
    (limit.isLimit _).isZero_pt
      ((Discrete.functor (fun n : ℕ ↦
        (DerivedCategory.homologyFunctor (ModuleCat.{r} R) i).obj (K.obj (op n)))).isZero
          (fun n ↦ hbounded (op n.as) i hi))
  have hzprod := hz.of_iso
    (PreservesProduct.iso (DerivedCategory.homologyFunctor (ModuleCat.{r} R) i)
      (fun n ↦ K.obj (op n)))
  exact hzprod.of_mono ((DerivedCategory.homologyFunctor (ModuleCat.{r} R) i).map p)

private theorem exists_pseudoCoherent_normalizedTower
    {C : Type r} [CommRing C] [IsNoetherianRing C]
    (J : Ideal C) [IsAdicComplete J C]
    [HasDerivedCategory.{w} (ModuleCat.{r} C)]
    [∀ n : ℕ, HasDerivedCategory.{w} (ModuleCat.{r} (C ⧸ J ^ (n + 1)))]
    [∀ n : ℕ, Finite (C ⧸ J ^ (n + 1))]
    (K : ∀ n : ℕ, DerivedCategory (ModuleCat.{r} (C ⧸ J ^ (n + 1))))
    (t : ∀ n : ℕ, K (n + 1) ⟶
      (ModuleCat.restrictScalars.{r} (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1))))).mapDerivedCategory.obj (K n))
    (hnorm : ∀ (n : ℕ) (N : DerivedCategory (ModuleCat.{r} (C ⧸ J ^ (n + 1)))),
      Function.Bijective (fun a : K n ⟶ N ↦ t n ≫
        (ModuleCat.restrictScalars.{r} (Ideal.Quotient.factor
          (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1))))).mapDerivedCategory.map a))
    (f : ∀ n : ℕ,
      (ModuleCat.restrictScalars.{r} (Ideal.Quotient.mk (J ^ (n + 2)))).mapDerivedCategory.obj
        (K (n + 1)) ⟶
      (ModuleCat.restrictScalars.{r} (Ideal.Quotient.mk (J ^ (n + 1)))).mapDerivedCategory.obj
        (K n))
    (hf : ∀ n : ℕ, f n =
      (ModuleCat.restrictScalars.{r} (Ideal.Quotient.mk (J ^ (n + 2)))).mapDerivedCategory.map
        (t n) ≫
      (Functor.mapDerivedCategoryCompIso
        (ModuleCat.restrictScalars.{r} (Ideal.Quotient.factor
          (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1)))))
        (ModuleCat.restrictScalars.{r} (Ideal.Quotient.mk (J ^ (n + 2))))).hom.app (K n) ≫
      (Functor.mapDerivedCategoryNatIso (ModuleCat.restrictScalarsComp'.{r}
        (Ideal.Quotient.mk (J ^ (n + 2)))
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1))))
        (Ideal.Quotient.mk (J ^ (n + 1)))
        (Ideal.Quotient.factor_comp_mk _).symm)).inv.app (K n))
    (a b : ℤ)
    (hbounded : ∀ (n : ℕ) (i : ℤ), (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{r} (C ⧸ J ^ (n + 1))) i).obj (K n)))
    (hfinite : ∀ (n : ℕ) (i : ℤ), Module.Finite (C ⧸ J ^ (n + 1))
      ((DerivedCategory.homologyFunctor
        (ModuleCat.{r} (C ⧸ J ^ (n + 1))) i).obj (K n))) :
    ∃ E : DerivedCategory (ModuleCat.{r} C),
      DerivedCategory.IsPseudoCoherent E ∧
      (∀ i : ℤ, (i < a ∨ b < i) →
        IsZero ((DerivedCategory.homologyFunctor _ i).obj E)) ∧
      ∀ (L : ∀ n : ℕ, DerivedCategory (ModuleCat.{r} C) ⥤
          DerivedCategory (ModuleCat.{r} (C ⧸ J ^ (n + 1))))
        (adj : ∀ n : ℕ, L n ⊣
          (ModuleCat.restrictScalars.{r}
            (Ideal.Quotient.mk (J ^ (n + 1)))).mapDerivedCategory),
        ∃ e : ∀ n : ℕ, (L n).obj E ≅ K n,
          ∀ (m n : ℕ) (h : n ≤ m),
            (adj m).unit.app E ≫
              (ModuleCat.restrictScalars.{r}
                (Ideal.Quotient.mk (J ^ (m + 1)))).mapDerivedCategory.map
                (e m).hom ≫
              (Functor.ofOpSequence (X := fun k : ℕ ↦
                (ModuleCat.restrictScalars.{r}
                  (Ideal.Quotient.mk (J ^ (k + 1)))).mapDerivedCategory.obj (K k))
                f).map (homOfLE h).op =
            (adj n).unit.app E ≫
              (ModuleCat.restrictScalars.{r}
                (Ideal.Quotient.mk (J ^ (n + 1)))).mapDerivedCategory.map
                (e n).hom := by
  classical
  let R (n : ℕ) := ModuleCat.restrictScalars.{r} (Ideal.Quotient.mk (J ^ (n + 1)))
  let D := Functor.ofOpSequence (X := fun n : ℕ ↦ (R n).mapDerivedCategory.obj (K n)) f
  obtain ⟨hP, _, _⟩ := derivedCategory_countableProducts_core.{0, w, r, r + 1}
    (ModuleCat.{r} C)
  let _ := hP
  obtain ⟨E, p, δ, hE⟩ := Pretriangulated.distinguished_cocone_triangle₁
    (towerTransitionEndomorphism (K := fun n : ℕ ↦ (R n).mapDerivedCategory.obj (K n)) f)
  have hT : IsDerivedLimitTriangle
      (K := fun n : ℕ ↦ (R n).mapDerivedCategory.obj (K n)) f E p δ := hE
  have hrec := DerivedCategory.pseudoCoherent_normalizedAlgebraTower J K t hnorm f hf
    E p δ hT ⟨b, fun i hi ↦ hbounded 0 i (Or.inr hi)⟩ (hfinite 0)
  have hfin : ∀ (n : ℕᵒᵖ) (i : ℤ),
      Finite ((DerivedCategory.homologyFunctor (ModuleCat.{r} C) i).obj (D.obj n)) := by
    intro n i
    have : Module.Finite (C ⧸ J ^ (n.unop + 1))
        ((DerivedCategory.homologyFunctor
          (ModuleCat.{r} (C ⧸ J ^ (n.unop + 1))) i).obj (K n.unop)) := hfinite n.unop i
    have : Finite ((DerivedCategory.homologyFunctor
        (ModuleCat.{r} (C ⧸ J ^ (n.unop + 1))) i).obj (K n.unop)) :=
      Module.finite_of_finite (C ⧸ J ^ (n.unop + 1))
    let e := ((R n.unop).mapDerivedCategoryHomologyFunctorIso i).app (K n.unop)
    change Finite ((DerivedCategory.homologyFunctor (ModuleCat.{r} C) i).obj
      ((R n.unop).mapDerivedCategory.obj (K n.unop)))
    exact Finite.of_equiv ((DerivedCategory.homologyFunctor
      (ModuleCat.{r} (C ⧸ J ^ (n.unop + 1))) i).obj (K n.unop)) e.toLinearEquiv.toEquiv
  have hvan : ∀ (n : ℕᵒᵖ) (i : ℤ), (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{r} C) i).obj (D.obj n)) := by
    intro n i hi
    exact (R n.unop).isZero_homologyFunctor_mapDerivedCategory_obj (hbounded n.unop i hi)
  have hDT : IsDerivedLimitTriangle
      (fun n ↦ D.map (homOfLE (Nat.le_succ n)).op) E p δ := by
    simpa only [D, Functor.ofOpSequence_map_homOfLE_succ] using hT
  refine ⟨E, hrec.1, module_derivedLimit_interval D E p δ hDT a b hfin hvan, ?_⟩
  intro L adj
  obtain ⟨e, _, hc, _, _⟩ := hrec.2 L adj
  exact ⟨e, hc⟩

private theorem completion_eval_ker {A : Type u} [CommRing A]
    (I : Ideal A) (hI : I.FG) (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ I n).toRingHom =
      (I.map (algebraMap A (AdicCompletion I A))) ^ n := by
  ext x
  trans x ∈ (AdicCompletion.eval I A n).ker
  · change AdicCompletion.evalₐ I n x = 0 ↔ AdicCompletion.eval I A n x = 0
    let h : (I ^ n • ⊤ : Ideal A) = I ^ n := by simp
    have hi : Function.Injective (Ideal.Quotient.factor h.le) := by
      simpa [RingHom.injective_iff_ker_eq_bot, Ideal.Quotient.factor_ker]
        using Ideal.map_mk_eq_bot_of_le h.ge
    rw [← AdicCompletion.factor_eval_eq_evalₐ I x h.le]
    exact map_eq_zero_iff (Ideal.Quotient.factor h.le) hi
  · rw [← AdicCompletion.pow_smul_top_eq_ker_eval hI, ← Ideal.map_pow]
    change x ∈ I ^ n • (⊤ : Submodule A (AdicCompletion I A)) ↔
      x ∈ (I ^ n).map (algebraMap A (AdicCompletion I A))
    rw [Ideal.smul_top_eq_map]
    rfl

private noncomputable def completionQuotientEquiv {A : Type u} [CommRing A]
    (I : Ideal A) (hI : I.FG) (n : ℕ) :
    (AdicCompletion I A ⧸ (I.map (algebraMap A (AdicCompletion I A))) ^ n) ≃+*
      (A ⧸ I ^ n) :=
  (Ideal.quotientEquivAlgOfEq A (completion_eval_ker I hI n).symm).toRingEquiv.trans
    ((AdicCompletion.evalₐ I n).toRingHom.quotientKerEquivOfSurjective
      (AdicCompletion.surjective_evalₐ I n))

/-- A lisse normalized tower is locally the finite-reduction system of an algebraic
pseudo-coherent complex over the completion. This provides a derived algebraic
object, without constructing a bounded complex of adic-lisse sheaves. -/
theorem lisse_tower_algebraic_derived_presentation
    (X Y : Scheme.{u}) [IsNoetherian X] (g : Y ⟶ X) [IsImmersion g]
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (M : AdicTower X d)
    (a b : ℤ) (hab : a ≤ b)
    (hbounded : ∀ (n : ℕ) (q : ℤ), (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (M.level n)))
    (hlisse : ∀ (n : ℕ) (q : ℤ),
      IsRelativelyFiniteLisseModule g (A ⧸ d.ideal ^ (n + 1))
        ((pbcRestrict ((adicTowerInverseImage g).map
          (pbcLevelConstantComparison X d n).hom)).obj
            ((DerivedCategory.homologyFunctor _ q).obj
              ((adicTowerPullback g ((pbcAdicRings X d).obj (op n))).obj (M.level n))))) :
    ∃ V : Sieve (⊤_ Y.ProEt), V ∈ ProEt.topology Y (⊤_ Y.ProEt) ∧
      ∀ (U : Y.ProEt) (f : U ⟶ ⊤_ Y.ProEt), V f →
        ∃ E : DerivedCategory (ModuleCat.{u + 1} (AdicCompletion d.ideal A)),
          DerivedCategory.IsPseudoCoherent E ∧
          (∀ q : ℤ, (q < a ∨ b < q) →
            IsZero ((DerivedCategory.homologyFunctor _ q).obj E)) ∧
          ∀ (φ : adicLisseConstantRing U.left (AdicCompletion d.ideal A) ⟶
      adicLisseCompletedRing U.left d.ideal)
            (_hφ : ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem U.left d.ideal) (op n) =
      (constantSheaf (ProEt.topology U.left) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ d.ideal (n + 1)).toRingHom))
            (β : (adicTowerInverseImage (U.hom ≫ g)).obj (adicLisseCompletedRing X d.ideal) ⟶
      adicLisseCompletedRing U.left d.ideal)
            (_hβ : ∀ n : ℕ, β ≫ limit.π (adicLisseRingSystem U.left d.ideal) (op n) =
      (adicTowerInverseImage (U.hom ≫ g)).map (limit.π (adicLisseRingSystem X d.ideal) (op n)) ≫
        proEtaleConstantInverseImageMap (U.hom ≫ g) CommRingCat.{u + 1}
          (CommRingCat.of (A ⧸ d.ideal ^ (n + 1)))),
            let c := completedConstantRealization U.left d.ideal φ ⋙ pbcRestrict β ⋙
      pbcRestrict ((adicTowerInverseImage (U.hom ≫ g)).map (pbcCompletedComparison X d).inv)
            ∀ (hc : c.Additive) (hlim : PreservesFiniteLimits c)
              (hcolim : PreservesFiniteColimits c),
              letI := hc
              letI := hlim
              letI := hcolim
              (∀ (n : ℕ) (q : ℤ),
                IsRelativelyFiniteLisseModule (U.hom ≫ g) (A ⧸ d.ideal ^ (n + 1))
                  ((pbcRestrict ((adicTowerInverseImage (U.hom ≫ g)).map
                    (pbcLevelConstantComparison X d n).hom)).obj
                      ((DerivedCategory.homologyFunctor _ q).obj
                        ((pbcDerivedExtend ((adicTowerInverseImage (U.hom ≫ g)).map
                  (pbcAdicProjection X d n))).obj (c.mapDerivedCategory.obj E))))) ∧
              ∃ e : ∀ n : ℕ, (pbcDerivedExtend ((adicTowerInverseImage (U.hom ≫ g)).map
                  (pbcAdicProjection X d n))).obj (c.mapDerivedCategory.obj E) ≅
                  (adicTowerPullback (U.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj
                    (M.level n),
                ∀ (m n : ℕ) (hnm : n ≤ m),
                  (e m).hom ≫ adicTowerRestrictedTransition d (U.hom ≫ g) M m n hnm =
                    pbcReductionTransition
                ((adicTowerInverseImage (U.hom ≫ g)).map (pbcAdicProjection X d m))
                ((adicTowerInverseImage (U.hom ≫ g)).map (pbcAdicQuotient X d m n hnm))
                ((adicTowerInverseImage (U.hom ≫ g)).map (pbcAdicProjection X d n))
                (((adicTowerInverseImage (U.hom ≫ g)).map_comp _ _).symm.trans
                  (congrArg (adicTowerInverseImage (U.hom ≫ g)).map
                    (pbcAdicProjection_comp X d m n hnm)))
                (c.mapDerivedCategory.obj E) ≫
                      (pbcDerivedRestrict ((adicTowerInverseImage (U.hom ≫ g)).map
                        (pbcAdicQuotient X d m n hnm))).map (e n).hom := by
  classical
  have _ := hab
  obtain ⟨V, hV, hlocal⟩ := lisse_tower_local_algebraic_reduction_diagram
    X Y g d M (fun n ↦ ⟨a, b, hbounded n⟩) hlisse
  refine ⟨V, hV, ?_⟩
  intro U f hf
  obtain ⟨K, t, hnorm, hbK, hfK, hrealize⟩ := hlocal U f hf
  let C := AdicCompletion d.ideal A
  let J := d.ideal.map (algebraMap A C)
  have : IsNoetherianRing A := d.noetherian
  obtain ⟨hC, hJ⟩ := AdicCompletion.isNoetherianRing_and_isAdicComplete_of_quotient
    d.ideal d.finitelyGenerated
  let _ := hC
  let _ := hJ
  have (n : ℕ) : Finite (C ⧸ J ^ (n + 1)) := by
    have := d.quotientFinite n
    exact Finite.of_equiv (A ⧸ d.ideal ^ (n + 1))
      (completionQuotientEquiv d.ideal d.finitelyGenerated (n + 1)).toEquiv.symm
  let R (n : ℕ) := ModuleCat.restrictScalars.{u + 1}
    (Ideal.Quotient.mk (J ^ (n + 1)))
  let s (n : ℕ) := (R (n + 1)).mapDerivedCategory.map (t n) ≫
    (Functor.mapDerivedCategoryCompIso
      (ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1)))))
      (R (n + 1))).hom.app (K n) ≫
    (Functor.mapDerivedCategoryNatIso (ModuleCat.restrictScalarsComp'.{u + 1}
      (Ideal.Quotient.mk (J ^ (n + 2)))
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1))))
      (Ideal.Quotient.mk (J ^ (n + 1)))
      (Ideal.Quotient.factor_comp_mk _).symm)).inv.app (K n)
  let D := Functor.ofOpSequence (X := fun n : ℕ ↦ (R n).mapDerivedCategory.obj (K n)) s
  let : HasLimits (ModuleCat.{u + 1} C) := ModuleCat.hasLimits'
  let : HasCountableProducts (ModuleCat.{u + 1} C) :=
    ⟨fun _ _ ↦ ModuleCat.hasLimitsOfShape⟩
  let : AB4StarOfSize.{0} (ModuleCat.{u + 1} C) :=
    AB4StarOfSize_shrink.{0, u + 1} _
  let : HasCountableProducts (DerivedCategory (ModuleCat.{u + 1} C)) :=
    derivedCategory_hasCountableProducts (ModuleCat.{u + 1} C)
  obtain ⟨E, p, δ, hE⟩ := Pretriangulated.distinguished_cocone_triangle₁
    (towerTransitionEndomorphism (K := fun n : ℕ ↦ (R n).mapDerivedCategory.obj (K n)) s)
  have hT : IsDerivedLimitTriangle
      (K := fun n : ℕ ↦ (R n).mapDerivedCategory.obj (K n)) s E p δ := hE
  have hrec := DerivedCategory.pseudoCoherent_normalizedAlgebraTower.{u + 1, 0, u + 1}
    J K t hnorm s
    (fun _ ↦ rfl) E p δ hT ⟨b, fun i hi ↦ hbK 0 i (hbounded 0 i (Or.inr hi))⟩ (hfK 0)
  have hfin : ∀ (n : ℕᵒᵖ) (i : ℤ),
      Finite ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} C) i).obj (D.obj n)) := by
    intro n i
    have : Module.Finite (C ⧸ J ^ (n.unop + 1))
        ((DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} (C ⧸ J ^ (n.unop + 1))) i).obj (K n.unop)) := hfK n.unop i
    have : Finite ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} (C ⧸ J ^ (n.unop + 1))) i).obj (K n.unop)) :=
      Module.finite_of_finite (C ⧸ J ^ (n.unop + 1))
    let e := ((R n.unop).mapDerivedCategoryHomologyFunctorIso i).app (K n.unop)
    change Finite ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} C) i).obj
      ((R n.unop).mapDerivedCategory.obj (K n.unop)))
    exact Finite.of_equiv ((DerivedCategory.homologyFunctor
      (ModuleCat.{u + 1} (C ⧸ J ^ (n.unop + 1))) i).obj (K n.unop)) e.toLinearEquiv.toEquiv
  have hvan : ∀ (n : ℕᵒᵖ) (i : ℤ), (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} C) i).obj (D.obj n)) := by
    intro n i hi
    exact (R n.unop).isZero_homologyFunctor_mapDerivedCategory_obj
      (hbK n.unop i (hbounded n.unop i hi))
  have hDT : IsDerivedLimitTriangle
      (fun n ↦ D.map (homOfLE (Nat.le_succ n)).op) E p δ := by
    simpa only [D, Functor.ofOpSequence_map_homOfLE_succ] using hT
  have hEvan := module_derivedLimit_interval D E p δ hDT a b hfin hvan
  have (n : ℕ) : (R n).mapDerivedCategory.IsRightAdjoint :=
    ModuleCat.derivedRestrictScalars_isRightAdjoint.{u + 1, 0}
      (Ideal.Quotient.mk (J ^ (n + 1)))
  let L (n : ℕ) := (R n).mapDerivedCategory.leftAdjoint
  let adj (n : ℕ) : L n ⊣ (R n).mapDerivedCategory := Adjunction.ofIsRightAdjoint _
  obtain ⟨e, _, he, _, _⟩ := hrec.2 L adj
  refine ⟨E, hrec.1, hEvan, ?_⟩
  exact fun φ hφ β hβ hc hlim hcolim ↦
    hrealize E L adj e he φ hφ β hβ hc hlim hcolim

end AlgebraicGeometry.Scheme
