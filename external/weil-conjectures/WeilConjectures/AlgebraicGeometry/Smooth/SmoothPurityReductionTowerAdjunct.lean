/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerData
import WeilConjectures.Algebra.Homology.System.SystemScalarGenerators
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement

set_option linter.privateModule false

/-! # Invertibility of the specified reduction adjuncts

Source: blueprint latest, normalized-towers-reduction, normalization paragraph;
Stacks Tags 06YY, 0G7E.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj

private theorem isIso_app_of_iso
    {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (τ : F ⟶ G) {K L : C} (e : K ≅ L)
    [IsIso (τ.app K)] : IsIso (τ.app L) := by
  exact IsIso.of_isIso_fac_left (τ.naturality e.hom)

private theorem opSequence_map_comp
    {C D : Type*} [Category* C] [Category* D]
    {X : ℕ → C} (f : ∀ n, X (n + 1) ⟶ X n) (G : C ⥤ D)
    {m n : ℕ} (h : m ≤ n) :
    G.map ((Functor.ofOpSequence f).map (homOfLE h).op) =
      (Functor.ofOpSequence (X := fun i ↦ G.obj (X i))
        (fun i ↦ G.map (f i))).map (homOfLE h).op := by
  let a : Functor.ofOpSequence f ⋙ G ⟶
      Functor.ofOpSequence (X := fun i ↦ G.obj (X i)) (fun i ↦ G.map (f i)) :=
    NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (by
      intro i
      simp only [Functor.comp_map, Functor.ofOpSequence_map_homOfLE_succ,
        Category.comp_id, Category.id_comp])
  simpa only [Functor.comp_map, a, NatTrans.ofOpSequence_app,
    Category.comp_id, Category.id_comp] using a.naturality (homOfLE h).op

section ScalarAdjunct
universe c v r
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
    {R S V : Sheaf J CommRingCat.{r}} {a : R ⟶ S} {b : S ⟶ V} {d : R ⟶ V}

private theorem scalar_adjunct_isIso (hd : d = a ≫ b)
    (A : SystemScalarModel a) (B : SystemScalarModel b) (D : SystemScalarModel d)
    (X : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R))
    (N : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S))
    (M : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J V))
    (en : N ≅ A.model.E.obj X) (em : M ≅ D.model.E.obj X)
    (t : N ⟶ (restrictScalars ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).map b)).obj M)
    (ht : ∀ U x,
      em.hom.val.app U (t.val.app U
        (en.inv.val.app U (systemModelTmul A.model X U 1 x))) =
      systemModelTmul D.model X U 1 x) :
    IsIso ((B.ordinaryAdj.homEquiv N M).symm t) := by
  let f := (B.ordinaryAdj.homEquiv N M).symm t
  let e := systemScalarModelComposition hd A B D
  have he : B.model.E.map en.inv ≫ f ≫ em.hom = e.hom.app X := by
    apply (B.ordinaryAdj.homEquiv _ _).injective
    rw [B.ordinaryAdj.homEquiv_naturality_left,
      B.ordinaryAdj.homEquiv_naturality_right, Equiv.apply_symm_apply]
    apply systemScalarModel_hom_ext A X _
    intro U x
    change em.hom.val.app U (t.val.app U
      (en.inv.val.app U (systemModelTmul A.model X U 1 x))) = _
    rw [ht]
    have hh := systemScalarModel_transpose_tmul B _ _ (e.hom.app X) U 1
      (systemModelTmul A.model X U 1 x)
    rw [one_smul] at hh
    calc
      _ = (e.hom.app X).val.app U
          (systemModelTmul B.model (A.model.E.obj X) U 1
            (systemModelTmul A.model X U 1 x)) := by
        simpa only [e, map_one, mul_one] using
          (systemScalarModelComposition_tmul hd A B D X U 1 1 x).symm
      _ = _ := hh
  have : IsIso (B.model.E.map en.inv ≫ f ≫ em.hom) := by
    rw [he]
    infer_instance
  have : IsIso (f ≫ em.hom) := IsIso.of_isIso_comp_left (B.model.E.map en.inv) _
  exact IsIso.of_isIso_comp_right f em.hom

private theorem scalar_adjunct_isIso_of_generators (hd : d = a ≫ b)
    (A : SystemScalarModel a) (B : SystemScalarModel b) (D : SystemScalarModel d)
    (X : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R))
    (N : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S))
    (M : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J V))
    (en : N ≅ A.model.E.obj X) (em : M ≅ D.model.E.obj X)
    (t : N ⟶ (restrictScalars ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).map b)).obj M)
    (ht : ∀ U x, @Eq (M.val.obj U)
      (t.val.app U (en.inv.val.app U (systemModelTmul A.model X U 1 x)))
      (em.inv.val.app U (systemModelTmul D.model X U 1 x))) :
    IsIso ((B.ordinaryAdj.homEquiv N M).symm t) := by
  apply scalar_adjunct_isIso hd A B D X N M en em t
  intro U x
  rw [ht]
  simp only [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app,
    ← SheafOfModules.comp_val, em.inv_hom_id, SheafOfModules.id_val,
    PresheafOfModules.id_app, ModuleCat.id_apply]

end ScalarAdjunct

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

private theorem coefficient_map_eq {m n : ℕ} (h : m ≤ n) :
    (sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        ((spCoefficientCommRings l E T).map (homOfLE h).op) =
      (spCoefficientRings l E T).map (homOfLE h).op := by
  unfold spCoefficientCommRings spCoefficientRings spCoefficientReduction
  exact opSequence_map_comp _ _ h

private theorem reduction_scalar_comp
    (coefficient : spIntegralSectionRing l E T ≅
      WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T)
    {m n : ℕ} (h : m ≤ n) :
    spIntegralReductionScalar l E T coefficient m =
      spIntegralReductionScalar l E T coefficient n ≫
        (spCoefficientCommRings l E T).map (homOfLE h).op := by
  apply (sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map_injective
  simp only [spIntegralReductionScalar, Functor.map_comp, Category.assoc]
  congr 1
  simp only [spIntegralEllProjection, Functor.map_preimage, Category.assoc]
  rw [coefficient_map_eq]
  rw [limit.w]

private theorem ordinary_reduction_isIso
    (D : SpCoefficientTowersAbelian l E T)
    (coefficient : spIntegralSectionRing l E T ≅
      WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T)
    (ordinary : spIntegralSectionModules l E T ⥤ spCoefficientTowers l E T)
    [ordinary.Additive]
    (level : spReductionOrdinaryLevels l E T D coefficient ordinary)
    (transition : IsSpReductionTransition l E T D coefficient ordinary level)
    {m n : ℕ} (h : m ≤ n) :
    ∀ X : spIntegralSectionModules l E T,
      IsIso ((D.ordinaryReduction h).app (ordinary.obj X)) := by
  let := D.hasDerived
  let := D.equivalenceAdditive
  let := D.evaluationLimits n
  let := D.evaluationColimits n
  let := D.evaluationLimits m
  let := D.evaluationColimits m
  intro X
  rw [D.ordinaryReduction_eq]
  apply scalar_adjunct_isIso_of_generators (reduction_scalar_comp l E T coefficient h)
    (D.scalar _) (D.scalar _) (D.scalar _) X
    ((D.equivalence.functor.obj (ordinary.obj X)).level n)
    ((D.equivalence.functor.obj (ordinary.obj X)).level m)
    ((level n).app X) ((level m).app X)
  intro U x
  have ht := transition X h U 1 x
  simp only [map_one, spStrictTransitionSection, spReductionGenerator] at ht
  exact ht

end AlgebraicGeometry.ProEtale
