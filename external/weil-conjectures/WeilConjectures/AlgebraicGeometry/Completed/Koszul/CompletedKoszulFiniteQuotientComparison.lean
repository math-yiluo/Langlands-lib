/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulTensorQuotientAugmentation
public import WeilConjectures.CategoryTheory.Flat.FlatConstantTensorProZeroConesSupplement
import all WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
import WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulRegularUnitNormalization
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement

/-! # Normalized completed finite quotient comparisons

Compare the actual completed coefficient presentation with the inverse limit of constant
quotient sheaves, apply the ordinary scalar-extension quotient theorem, and then pass to
complexes concentrated in degree zero.

Source: Stacks Project, Tags 093M and 099M.
(blueprint: new-s3-completed-koszul-finite-quotient-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.unusedVariables false
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme
private instance comparisonAbLocallyBijective (X : Scheme.{t}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0} X

attribute [local instance] koszulConstantFunctor_preservesZero
local instance finiteQuotientComparisonCochainMonoidal
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A) :
    MonoidalCategory (CochainComplex (CompletedAdicModules T d) ℤ) :=
  CategoryTheory.flatConstantCochainMonoidal
    (J := ProEt.topology T) (O := completedAdicCommRing T d)
local instance finiteQuotientComparisonCochainMonoidalStruct
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A) :
    MonoidalCategoryStruct (CochainComplex (CompletedAdicModules T d) ℤ) :=
  (finiteQuotientComparisonCochainMonoidal T d).toMonoidalCategoryStruct

private lemma liftedSpan (A : Type t) [CommRing A] (r : ℕ) (a : Fin r → A) :
    (Ideal.span (Set.range (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A)))).map
      (ULift.ringEquiv : ULift.{t + 1} A ≃+* A).toRingHom =
      Ideal.span (Set.range a) := by
  rw [Ideal.map_span]
  congr 1
  ext x
  simp [ULift.ringEquiv]

open AdicCoefficients

-- Constant finite quotients and their completed coefficient presentation.

private def finiteConstantIso (T : Scheme.{t}) (Λ : Type (t + 1))
    [CommRing Λ] [Finite Λ] :
    (adicLisseForget T).obj (adicLisseConstantRing T Λ) ≅
      finiteRingPresentation T Λ := by
  let := CompletedConstantReduction.constantComparison_isIso T Λ
  exact (adicLisseForget T).mapIso (asIso (constantComparison T Λ)) ≪≫
    finiteRingComparison T Λ

private lemma finiteConstantIso_unit (T : Scheme.{t}) (Λ : Type (t + 1))
    [CommRing Λ] [Finite Λ] :
    let : TopologicalSpace Λ := ⊥
    let : DiscreteTopology Λ := ⟨rfl⟩
    adicLisseConstantUnit T Λ ≫ (finiteConstantIso T Λ).hom.hom =
      ProEtale.finiteCoefficientScalarMap T Λ := by
  change Functor.whiskerRight (toSheafify (ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of Λ))) (forget₂ CommRingCat RingCat) ≫
      (Functor.whiskerRight (constantComparison T Λ).hom (forget₂ CommRingCat RingCat) ≫
        (finiteRingComparison_exists T Λ).choose.hom) = _
  dsimp only [constantComparison, constantSheaf, Functor.comp_map]
  rw [← Category.assoc, ← Functor.whiskerRight_comp, ← toSheafify_naturality,
    Functor.whiskerRight_comp, Category.assoc]
  change _ ≫ (Functor.whiskerRight (toSheafify (ProEt.topology T)
    (functionPresheaf T Λ)) (forget₂ CommRingCat RingCat) ≫
      (finiteRingComparison_exists T Λ).choose.hom) = _
  rw [(finiteRingComparison_exists T Λ).choose_spec.1.2]
  rfl

private def liftedQuotientEquiv (T : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (r : ℕ) (a : Fin r → A)
    (ha : Ideal.span (Set.range a) = d.ideal) (n : ℕ) :
    ((ULift.{t + 1} A) ⧸
      (Ideal.span (Set.range (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A)))) ^
        (n + 1)) ≃+* completedAdicQuotient d n :=
  (Ideal.quotientEquiv _ _ (ULift.ringEquiv : ULift.{t + 1} A ≃+* A)
    (by
      change d.ideal ^ (n + 1) =
        Ideal.map (ULift.ringEquiv : ULift.{t + 1} A ≃+* A).toRingHom _
      rw [Ideal.map_pow, liftedSpan, ha])).trans ULift.ringEquiv.symm

private lemma liftedQuotientEquiv_mk (T : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (r : ℕ) (a : Fin r → A)
    (ha : Ideal.span (Set.range a) = d.ideal) (n : ℕ) (x : ULift.{t + 1} A) :
    liftedQuotientEquiv T d r a ha n (Ideal.Quotient.mk _ x) =
      ULift.up (Ideal.Quotient.mk (d.ideal ^ (n + 1)) x.down) := rfl

private def quotientRingIso (T : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (r : ℕ) (a : Fin r → A)
    (ha : Ideal.span (Set.range a) = d.ideal) (n : ℕ) :
    (adicLisseForget T).obj (adicLisseConstantRing T
      ((ULift.{t + 1} A) ⧸
        (Ideal.span (Set.range (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A)))) ^
          (n + 1))) ≅ completedAdicFiniteRing T d n :=
  (adicLisseForget T).mapIso ((constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).mapIso
    (liftedQuotientEquiv T d r a ha n).toCommRingCatIso) ≪≫
      finiteConstantIso T (completedAdicQuotient d n)

private lemma quotientRingIso_unit (T : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (r : ℕ) (a : Fin r → A)
    (ha : Ideal.span (Set.range a) = d.ideal) (n : ℕ) (V : T.ProEtᵒᵖ)
    (x : (ULift.{t + 1} A) ⧸
      (Ideal.span (Set.range (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A)))) ^ (n + 1)) :
    (quotientRingIso T d r a ha n).hom.hom.app V
      ((adicLisseConstantUnit T _).app V x) =
        (ProEtale.finiteCoefficientScalarMap T (completedAdicQuotient d n)).app V
          (liftedQuotientEquiv T d r a ha n x) := by
  let q := (liftedQuotientEquiv T d r a ha n).toCommRingCatIso
  have hn := toSheafify_naturality (ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).map q.hom)
  have hn' := congrArg (fun f ↦ f.app V x) hn
  change (finiteConstantIso T (completedAdicQuotient d n)).hom.hom.app V
    (((constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map q.hom).hom.app V
      ((adicLisseConstantUnit T _).app V x)) = _
  have hunit := congrArg (fun f ↦ f.app V (liftedQuotientEquiv T d r a ha n x))
    (finiteConstantIso_unit T (completedAdicQuotient d n))
  exact (congrArg ((finiteConstantIso T (completedAdicQuotient d n)).hom.hom.app V)
    hn'.symm).trans hunit

private lemma constantRing_hom_ext (T : Scheme.{t}) (Λ : Type (t + 1)) [CommRing Λ]
    {H : Sheaf (ProEt.topology T) RingCat.{t + 1}}
    (f g : (adicLisseForget T).obj (adicLisseConstantRing T Λ) ⟶ H)
    (h : ∀ (V : T.ProEtᵒᵖ) (x : Λ),
      f.hom.app V ((adicLisseConstantUnit T Λ).app V x) =
        g.hom.app V ((adicLisseConstantUnit T Λ).app V x)) : f = g := by
  ext V x
  have hs := (isSheaf_iff_isSheaf_of_type (ProEt.topology T)
    (H.obj ⋙ CategoryTheory.forget RingCat.{t + 1})).1
      ((sheafCompose (ProEt.topology T) (CategoryTheory.forget RingCat.{t + 1})).obj H).property
  apply (hs.isSeparated _ (Presheaf.imageSieve_mem (ProEt.topology T)
    (adicLisseConstantUnit T Λ) x)).ext
  rintro W j ⟨b, hb⟩
  change H.obj.map j.op (f.hom.app V x) = H.obj.map j.op (g.hom.app V x)
  rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, ← hb]
  exact h _ b

private lemma finiteStep_scalar (T : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) (V : T.ProEtᵒᵖ)
    (x : completedAdicQuotient d (n + 1)) :
    (completedAdicFiniteStep T d n).hom.app V
      ((ProEtale.finiteCoefficientScalarMap T (completedAdicQuotient d (n + 1))).app V x) =
    (ProEtale.finiteCoefficientScalarMap T (completedAdicQuotient d n)).app V
      (RingHom.ulift (adicQuotientMap d.ideal (n + 2) (n + 1) (Nat.le_succ _)) x) := by
  have hs := congrArg
    (fun k ↦ (k.app V).hom
      ((ProEtale.finiteCoefficientConstants T
        (completedAdicQuotient d (n + 1))).app V x))
    (toSheafify_naturality (ProEt.topology T) (completedAdicFinitePresheafStep T d n))
  have hc : (completedAdicFinitePresheafStep T d n).app V
      ((ProEtale.finiteCoefficientConstants T (completedAdicQuotient d (n + 1))).app V x) =
    (ProEtale.finiteCoefficientConstants T (completedAdicQuotient d n)).app V
      (RingHom.ulift (adicQuotientMap d.ideal (n + 2) (n + 1) (Nat.le_succ _)) x) := by
    apply ContinuousMap.ext
    intro y
    rfl
  simp only [NatTrans.comp_app, RingCat.comp_apply] at hs
  rw [hc] at hs
  exact hs.symm

private lemma constantMap_unit (T : Scheme.{t}) {R S : Type (t + 1)}
    [CommRing R] [CommRing S] (f : R →+* S) (V : T.ProEtᵒᵖ) (x : R) :
    (((constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
      (CommRingCat.ofHom f)).hom.app V)
        ((adicLisseConstantUnit T R).app V x) =
      (adicLisseConstantUnit T S).app V (f x) := by
  exact (congrArg (fun k ↦ k.app V x) (toSheafify_naturality (ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).map (CommRingCat.ofHom f)))).symm

private def quotientSystemIso (T : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (r : ℕ) (a : Fin r → A)
    (ha : Ideal.span (Set.range a) = d.ideal) :
    adicLisseRingSystem T
      (Ideal.span (Set.range (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A)))) ⋙
        adicLisseForget T ≅ completedAdicRingSystem T d := by
  refine NatIso.ofComponents (fun n ↦ quotientRingIso T d r a ha n.unop) ?_
  intro m n f
  let z := NatTrans.ofOpSequence
    (F := adicLisseRingSystem T
      (Ideal.span (Set.range (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A)))) ⋙
        adicLisseForget T)
    (G := completedAdicRingSystem T d)
    (fun k ↦ (quotientRingIso T d r a ha k).hom) (by
      intro k
      apply constantRing_hom_ext
      intro V x
      simp only [Functor.comp_map, adicLisseRingSystem, completedAdicRingSystem,
        Functor.ofOpSequence_map_homOfLE_succ]
      change (quotientRingIso T d r a ha k).hom.hom.app V
        (((constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
          (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc _ (k + 1)))).hom.app V
            ((adicLisseConstantUnit T _).app V x)) =
        (completedAdicFiniteStep T d k).hom.app V
          ((quotientRingIso T d r a ha (k + 1)).hom.hom.app V
            ((adicLisseConstantUnit T _).app V x))
      rw [constantMap_unit, quotientRingIso_unit, quotientRingIso_unit, finiteStep_scalar]
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl)
  exact z.naturality f

private instance comparisonForgetPreservesLimit (T : Scheme.{t})
    (D : ℕᵒᵖ ⥤ Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :
    PreservesLimit D (adicLisseForget T) := by
  let F := adicLisseForget T
  have : PreservesLimit D
      (F ⋙ sheafToPresheaf (ProEt.topology T) RingCat.{t + 1}) :=
    inferInstanceAs (PreservesLimit D
      (sheafToPresheaf (ProEt.topology T) CommRingCat.{t + 1} ⋙
        (Functor.whiskeringRight T.ProEtᵒᵖ CommRingCat.{t + 1} RingCat.{t + 1}).obj
          (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})))
  exact preservesLimit_of_reflects_of_preserves F
    (sheafToPresheaf (ProEt.topology T) RingCat.{t + 1})

private def completionRingIso (T : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (r : ℕ) (a : Fin r → A)
    (ha : Ideal.span (Set.range a) = d.ideal) :
    adicLisseCompletedRing T
      (Ideal.span (Set.range (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A)))) ≅
        completedAdicCommRing T d :=
  (adicLisseForget T).preimageIso
    (preservesLimitIso (adicLisseForget T) _ ≪≫
      lim.mapIso (quotientSystemIso T d r a ha))

private lemma completionRingIso_projection (T : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (r : ℕ) (a : Fin r → A)
    (ha : Ideal.span (Set.range a) = d.ideal) (n : ℕ) :
    (adicLisseForget T).map (completionRingIso T d r a ha).hom ≫
      completedAdicProjection T d n =
    (adicLisseForget T).map (limit.π (adicLisseRingSystem T
      (Ideal.span (Set.range (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A))))) (op n)) ≫
        (quotientRingIso T d r a ha n).hom := by
  unfold completionRingIso
  rw [Functor.preimageIso, Functor.map_preimage]
  change ((preservesLimitIso _ _).hom ≫ lim.map (quotientSystemIso T d r a ha).hom) ≫ _ = _
  dsimp only [completedAdicProjection]
  erw [Category.assoc, limMap_π, ← Category.assoc, preservesLimitIso_hom_π]
  rfl

private lemma inverse_projection {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {X Y Q : C} (e : X ≅ Y) {Z : D} (p : F.obj Y ⟶ Z)
    (q : X ⟶ Q) (k : F.obj Q ⟶ Z)
    (h : F.map e.hom ≫ p = F.map q ≫ k) :
    F.map e.inv ≫ F.map q ≫ k = p := by
  rw [← h, ← Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id, F.map_id, Category.id_comp]

private lemma completionRingIso_scalar (T : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (r : ℕ) (a : Fin r → A)
    (ha : Ideal.span (Set.range a) = d.ideal) (n : ℕ) :
    completedAdicScalar T d ≫ (completionRingIso T d r a ha).inv ≫
      limit.π (adicLisseRingSystem T
        (Ideal.span (Set.range (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A))))) (op n) =
      (constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk
          ((Ideal.span (Set.range (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A)))) ^
            (n + 1)))) := by
  apply (adicLisseForget T).map_injective
  simp only [Functor.map_comp]
  apply (cancel_mono (quotientRingIso T d r a ha n).hom).1
  simp only [Category.assoc]
  have hinv := inverse_projection (adicLisseForget T)
    (completionRingIso T d r a ha) (completedAdicProjection T d n)
    (limit.π (adicLisseRingSystem T
      (Ideal.span (Set.range (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A))))) (op n))
    (quotientRingIso T d r a ha n).hom (completionRingIso_projection T d r a ha n)
  refine (congrArg (fun k ↦ (adicLisseForget T).map (completedAdicScalar T d) ≫ k)
    hinv).trans ?_
  apply constantRing_hom_ext
  intro V x
  change (completedAdicProjection T d n).hom.app V
    ((completedAdicScalar T d).hom.app V ((adicLisseConstantUnit T _).app V x)) =
      (quotientRingIso T d r a ha n).hom.hom.app V
        ((((constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
          (CommRingCat.ofHom (Ideal.Quotient.mk _))).hom.app V)
            ((adicLisseConstantUnit T _).app V x))
  rw [constantMap_unit, quotientRingIso_unit, liftedQuotientEquiv_mk]
  exact (completedAdicScalar_exists T d).exists.choose_spec n V x

-- The quotient map is constructed before its invertibility is invoked.

private theorem presentedReduction_exists (T : Scheme.{t})
    {B : Type (t + 1)} [CommRing B] (I : Ideal B)
    {S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (c : adicLisseConstantRing T B ⟶ S)
    (p : S ⟶ adicLisseConstantRing T (B ⧸ I))
    (hc : c ≫ p = (constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
      (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    ∃ f : (completedAdicChange T c).obj
        ((adicLisseConstantModules T B).obj (ModuleCat.of B (B ⧸ I))) ⟶
      (SheafOfModules.restrictScalars ((adicLisseForget T).map p)).obj
        (SheafOfModules.unit (adicLisseRing T (B ⧸ I))),
      ∀ (V : T.ProEtᵒᵖ) (s : S.obj.obj V) (x : B ⧸ I),
        f.val.app V (tensorSection T c _ V s
          ((toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
            (AddCommGrpCat.of (B ⧸ I)))).app V x)) =
          p.hom.app V s * @id ((adicLisseConstantRing T (B ⧸ I)).obj.obj V)
            ((adicLisseConstantUnit T (B ⧸ I)).app V x) := by
  let Q := B ⧸ I
  let M := (adicLisseConstantModules T B).obj (ModuleCat.of B Q)
  let H := (SheafOfModules.restrictScalars ((adicLisseForget T).map p)).obj
    (SheafOfModules.unit (adicLisseRing T Q))
  let N := (SheafOfModules.restrictScalars ((adicLisseForget T).map c)).obj H
  let P := (siteConstantModulePresheafGeneral (C := T.ProEt) B).obj (ModuleCat.of B Q)
  let g₀ : P ⟶
      (PresheafOfModules.restrictScalars (adicLisseConstantUnit T B)).obj N.val :=
    { app := fun V ↦ ModuleCat.ofHom
        (Y := ((PresheafOfModules.restrictScalars
          (adicLisseConstantUnit T B)).obj N.val).obj V)
        { toFun := fun x ↦ (adicLisseConstantUnit T Q).app V x
          map_add' := map_add _
          map_smul' := by
            intro b x
            have h := congrArg (fun k ↦ k.hom.app V
              ((adicLisseConstantUnit T B).app V b)) hc
            change p.hom.app V (c.hom.app V
              ((adicLisseConstantUnit T B).app V b)) = _ at h
            change (adicLisseConstantUnit T Q).app V ((Ideal.Quotient.mk I) b * x) =
              p.hom.app V (c.hom.app V
                ((adicLisseConstantUnit T B).app V b)) *
                  @id ((adicLisseConstantRing T Q).obj.obj V)
                    ((adicLisseConstantUnit T Q).app V x)
            rw [h, constantMap_unit, map_mul]
            rfl }
      naturality := by
        intro V W j
        ext x
        exact ConcreteCategory.congr_hom ((adicLisseConstantUnit T Q).naturality j) x }
  let g : M ⟶ N := (PresheafOfModules.sheafificationHomEquiv.{t + 1}
    (adicLisseConstantUnit T B) (P := P) (F := N)).symm g₀
  let h := (completedAdicChangeData T c).choose_spec.choose M
  let f₀ := (CompletedConstantReduction.tensorHomEquiv T c M H).symm g
  let f := eqToHom h ≫ f₀
  refine ⟨f, ?_⟩
  intro V s x
  change (eqToHom h.symm ≫ f).val.app V
    ((toSheafify (ProEt.topology T)
      (SheafOfModules.changeOfRingsPresheaf c M).presheaf).app V
        (s ⊗ₜ[(adicLisseConstantRing T B).obj.obj V, (c.hom.app V).hom]
          ((toSheafify (ProEt.topology T) P.presheaf).app V x))) = _
  have hf : eqToHom h.symm ≫ f = f₀ := by simp [f]
  rw [hf]
  rw [CompletedConstantReduction.tensorHomEquiv_tmul,
    Equiv.apply_symm_apply]
  have hg := (PresheafOfModules.sheafificationHomEquiv.{t + 1}
    (adicLisseConstantUnit T B) (P := P) (F := N)).apply_symm_apply g₀
  have hg' := congrArg (fun k ↦ k.app V x) hg
  change g.val.app V ((toSheafify (ProEt.topology T) P.presheaf).app V x) =
    (adicLisseConstantUnit T Q).app V x at hg'
  change p.hom.app V s * @id ((adicLisseConstantRing T Q).obj.obj V)
    (g.val.app V ((toSheafify (ProEt.topology T) P.presheaf).app V x)) = _
  rw [hg']

private def unitRestrictionIso {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R H K : Sheaf J RingCat.{t + 1}} (p : R ⟶ H) (q : R ⟶ K) (e : H ≅ K)
    (h : p ≫ e.hom = q) :
    (SheafOfModules.restrictScalars.{t + 1} p).obj (SheafOfModules.unit H) ≅
      (SheafOfModules.restrictScalars.{t + 1} q).obj (SheafOfModules.unit K) := by
  refine (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (fun V ↦ LinearEquiv.toModuleIso
      (show ((SheafOfModules.restrictScalars p).obj
          (SheafOfModules.unit H)).val.obj V ≃ₗ[R.obj.obj V]
        ((SheafOfModules.restrictScalars q).obj
          (SheafOfModules.unit K)).val.obj V from
      { toFun := e.hom.hom.app V
        invFun := e.inv.hom.app V
        left_inv := fun x ↦ congrArg (fun k ↦ k.hom.app V x) e.hom_inv_id
        right_inv := fun x ↦ congrArg (fun k ↦ k.hom.app V x) e.inv_hom_id
        map_add' := map_add _
        map_smul' := by
          intro s x
          change e.hom.hom.app V (p.hom.app V s * @id (H.obj.obj V) x) =
            q.hom.app V s * e.hom.hom.app V x
          rw [map_mul]
          exact congrArg (fun y ↦ y * e.hom.hom.app V x)
            (congrArg (fun k ↦ k.hom.app V s) h) })) ?_)
  intro V W j
  ext x
  exact NatTrans.naturality_apply e.hom.hom j x

-- Keep coefficient rings symbolic in the scalar-unit calculation.
private lemma scalarRegular_one
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{t + 1}]
    [HasWeakSheafify J AddCommGrpCat.{t + 1}]
    {R S : Sheaf J CommRingCat.{t + 1}} (φ : R ⟶ S)
    (G : SheafOfModules.{t + 1} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      SheafOfModules.{t + 1} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (h : ∀ M, G.obj M = SheafOfModules.changeOfRings φ M)
    {M : SheafOfModules.{t + 1} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (u : SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⟶ M)
    (hm : G.map u = eqToHom (h _) ≫
      SheafOfModules.changeOfRingsHom φ _ u ≫ eqToHom (h M).symm)
    (V : Cᵒᵖ) :
    ((scalarUnitIso φ).inv ≫ eqToHom (h _).symm ≫ G.map u).val.app V
      (1 : S.obj.obj V) =
      (eqToHom (h M).symm).val.app V
        ((toSheafify J (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app V
          ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom]
            (u.val.app V (1 : R.obj.obj V)))) := by
  change (G.map u).val.app V ((eqToHom (h _).symm).val.app V
    ((scalarUnitIso φ).inv.val.app V (1 : S.obj.obj V))) = _
  rw [scalarUnitIso_inv_one]
  exact normalizedScalarTensor_map φ G h u hm V 1 (1 : R.obj.obj V)

attribute [local irreducible] completedAdicRing completedAdicChangeData

private lemma comparisonScalarTensor_map (T : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) {M N : SheafOfModules.{t + 1} (adicModuleRing T A)}
    (f : M ⟶ N) (V : T.ProEtᵒᵖ) (s : (completedAdicCommRing T d).obj.obj V)
    (x : M.val.obj V) :
    ((completedAdicScalarExtension T d).map f).val.app V
      (completedAdicScalarTensor T d M V s x) =
        completedAdicScalarTensor T d N V s (f.val.app V x) := by
  exact normalizedScalarTensor_map (completedAdicScalar T d) (completedAdicScalarExtension T d)
    (completedAdicScalarExtensionData T d).choose_spec.choose f
    ((completedAdicScalarExtensionData T d).choose_spec.choose_spec.choose f) V s x

private lemma regularUnitIso_one (T : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (V : T.ProEtᵒᵖ) :
    (completedRegularUnitIso T d).hom.val.app V (1 : (completedAdicRing T d).obj.obj V) =
      completedAdicScalarTensor T d
        ((koszulConstantFunctor T A).obj
          (ModuleCat.of (ULift.{t + 1} A) (ULift.{t + 1} A))) V 1
        ((toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{t + 1} A)))).app V (1 : ULift.{t + 1} A)) := by
  let G := completedAdicScalarExtension T d
  let hG := (completedAdicScalarExtensionData T d).choose_spec.choose
  have h := scalarRegular_one (completedAdicScalar T d) G hG (koszulConstantOne T A)
    ((completedAdicScalarExtensionData T d).choose_spec.choose_spec.choose _) V
  unfold completedRegularUnitIso
  refine h.trans ?_
  exact congrArg (fun x ↦ completedAdicScalarTensor T d _ V 1 x)
    ((koszulConstantOne_exists T A).exists.choose_spec V)

private theorem quotientModuleIso_exists (T : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (r : ℕ) (a : Fin r → A)
    (ha : Ideal.span (Set.range a) = d.ideal) (n : ℕ) :
    let E := koszulConstantFunctor T A ⋙ completedAdicScalarExtension T d
    let I := Ideal.span (Set.range (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A)))
    ∃ e : E.obj (ModuleCat.of (ULift.{t + 1} A) ((ULift.{t + 1} A) ⧸ I ^ (n + 1))) ≅
        completedAdicFiniteModule T d n,
      (completedRegularUnitIso T d).hom ≫ E.map (ModuleCat.ofHom (I ^ (n + 1)).mkQ) ≫
        e.hom = reconstructionQuotientUnit T d n := by
  let B := ULift.{t + 1} A
  let I := Ideal.span (Set.range (fun i ↦ (ULift.up (a i) : B)))
  let c := completedAdicScalar T d
  let e := completionRingIso T d r a ha
  let p := e.inv ≫ limit.π (adicLisseRingSystem T I) (op n)
  have hc : c ≫ p = (constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
      (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) :=
    completionRingIso_scalar T d r a ha n
  obtain ⟨f, hf⟩ := presentedReduction_exists T (I ^ (n + 1)) c p hc
  let : IsNoetherianRing A := d.noetherian
  let : IsNoetherianRing B := isNoetherianRing_of_surjective A B
    (ULift.ringEquiv : B ≃+* A).symm.toRingHom (ULift.ringEquiv.symm.surjective)
  have hiso : IsIso f := (completed_constant_algebra_flat_quotients T I
    (completedAdicCommRing T d) e c (completionRingIso_scalar T d r a ha)).2.2 n _
      (Iso.refl _) p (by
        change p = p ≫ 𝟙 _
        exact (Category.comp_id p).symm) f (by
        intro V s x
        exact hf V s x)
  let := hiso
  let k := quotientRingIso T d r a ha n
  have hp : (adicLisseForget T).map p ≫ k.hom = completedAdicProjection T d n := by
    simpa only [p, Functor.map_comp, Category.assoc] using
      inverse_projection (adicLisseForget T) e (completedAdicProjection T d n)
        (limit.π (adicLisseRingSystem T I) (op n)) k.hom
        (completionRingIso_projection T d r a ha n)
  let ek := unitRestrictionIso ((adicLisseForget T).map p)
    (completedAdicProjection T d n) k hp
  refine ⟨asIso f ≪≫ ek, ?_⟩
  apply (completedAdicFiniteModule T d n).unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro V
  change (ek.hom.val.app V)
    (f.val.app V (((completedAdicScalarExtension T d).map
      ((koszulConstantFunctor T A).map (ModuleCat.ofHom (I ^ (n + 1)).mkQ))).val.app V
        ((completedRegularUnitIso T d).hom.val.app V
          (1 : (completedAdicRing T d).obj.obj V)))) =
      (reconstructionQuotientUnit T d n).val.app V
        (1 : (completedAdicRing T d).obj.obj V)
  rw [regularUnitIso_one]
  rw [comparisonScalarTensor_map]
  have hmap := toSheafify_naturality (ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).map
      (AddCommGrpCat.ofHom (I ^ (n + 1)).mkQ.toAddMonoidHom))
  have hmap' := (congrArg (fun k ↦ k.app V (1 : B)) hmap).symm
  change (((koszulConstantFunctor T A).map (ModuleCat.ofHom
      (I ^ (n + 1)).mkQ)).val.app V)
    ((toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
      (AddCommGrpCat.of B))).app V (1 : B)) =
    (toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
      (AddCommGrpCat.of (B ⧸ I ^ (n + 1))))).app V (Ideal.Quotient.mk _ 1) at hmap'
  rw [hmap']
  change ek.hom.val.app V
    (f.val.app V (tensorSection T c _ V 1
      ((toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
        (AddCommGrpCat.of (B ⧸ I ^ (n + 1))))).app V (1 : B ⧸ I ^ (n + 1))))) = _
  rw [hf]
  simp only [map_one, one_mul]
  change k.hom.hom.app V (1 : (adicLisseConstantRing T
    (B ⧸ I ^ (n + 1))).obj.obj V) = _
  rw [map_one]
  exact ((reconstructionQuotientUnit_exists T d n).exists.choose_spec V).symm

-- Passing from modules to complexes uses only concentration in degree zero.

private def concentratedIso {C : Type*} [Category* C] [HasZeroMorphisms C]
    (K L : CochainComplex C ℤ) (e : K.X 0 ≅ L.X 0)
    (hK : ∀ i : ℤ, i ≠ 0 → IsZero (K.X i))
    (hL : ∀ i : ℤ, i ≠ 0 → IsZero (L.X i)) : K ≅ L := by
  refine HomologicalComplex.Hom.isoOfComponents (fun i ↦
    if hi : i = 0 then eqToIso (congrArg K.X hi) ≪≫ e ≪≫
      (eqToIso (congrArg L.X hi)).symm else (hK i hi).iso (hL i hi)) ?_
  intro i j hij
  by_cases hi : i = 0
  · subst i
    have hj : j ≠ 0 := by
      change (0 : ℤ) + 1 = j at hij
      omega
    exact (hL j hj).eq_of_tgt _ _
  · exact (hK i hi).eq_of_src _ _

private lemma concentratedIso_zero {C : Type*} [Category* C] [HasZeroMorphisms C]
    (K L : CochainComplex C ℤ) (e : K.X 0 ≅ L.X 0)
    (hK : ∀ i : ℤ, i ≠ 0 → IsZero (K.X i))
    (hL : ∀ i : ℤ, i ≠ 0 → IsZero (L.X i)) :
    (concentratedIso K L e hK hL).hom.f 0 = e.hom := by
  simp [concentratedIso]

private lemma quotientUnit_normalization {C : Type*} [Category* C] [MonoidalCategory C]
    {X : C} (e : X ≅ 𝟙_ C) (Q : C) (q : 𝟙_ C ⟶ Q) :
    ((ρ_ X).inv ≫ X ◁ q) ≫ (e.hom ▷ Q ≫ (λ_ Q).hom) = e.hom ≫ q := by
  simp only [Category.assoc]
  rw [whisker_exchange_assoc, leftUnitor_naturality,
    unitors_equal, rightUnitor_naturality_assoc, Iso.inv_hom_id_assoc]

/-- A finite quotient comparison, isolated from exactness of the coefficient functor.
Source: Stacks Project, Tags 099M, 0921 and 093M.
(blueprint: new-s3-completed-koszul-finite-quotient-comparison). -/
theorem completedKoszulFiniteQuotientComparison
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) :
    let E := koszulConstantFunctor T A ⋙ completedAdicScalarExtension T d
    let U := 𝟙_ (CochainComplex (CompletedAdicModules T d) ℤ)
    ∃ (c : U.X 0 ≅ E.obj (ModuleCat.of (ULift.{t + 1} A) (ULift.{t + 1} A)))
      (eQ : ∀ n : ℕ, (E.mapHomologicalComplex (.up ℤ)).obj
        (((ChainComplex.single₀ (ModuleCat.{t + 1} (ULift.{t + 1} A))).obj
          (ModuleCat.of (ULift.{t + 1} A)
            ((ULift.{t + 1} A) ⧸
              (Ideal.span (Set.range (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A)))) ^
                (n + 1)))).extend ComplexShape.embeddingDownNat) ≅
        (((completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ)).obj U).asFunctor.obj
          (op n)),
      ∀ n : ℕ, c.hom ≫ E.map (ModuleCat.ofHom
        ((Ideal.span (Set.range (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A)))) ^
          (n + 1)).mkQ) ≫
        E.map ((((ChainComplex.single₀ (ModuleCat.{t + 1} (ULift.{t + 1} A))).obj
          (ModuleCat.of (ULift.{t + 1} A)
            ((ULift.{t + 1} A) ⧸
              (Ideal.span (Set.range (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A)))) ^
                (n + 1)))).extendXIso ComplexShape.embeddingDownNat (i := 0) rfl).inv) ≫
        (eQ n).hom.f 0 = (completedQuotientTensorUnit T d U n).f 0 := by
  classical
  let E := koszulConstantFunctor T A ⋙ completedAdicScalarExtension T d
  let U := 𝟙_ (CochainComplex (CompletedAdicModules T d) ℤ)
  let I := Ideal.span (Set.range (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A)))
  let Q (n : ℕ) := ModuleCat.of (ULift.{t + 1} A) ((ULift.{t + 1} A) ⧸ I ^ (n + 1))
  let S (n : ℕ) := (ChainComplex.single₀ (ModuleCat.{t + 1} (ULift.{t + 1} A))).obj (Q n)
  let K (n : ℕ) := (E.mapHomologicalComplex (.up ℤ)).obj
    ((S n).extend ComplexShape.embeddingDownNat)
  let L (n : ℕ) := (((completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ)).obj
    U).asFunctor.obj (op n)
  let u : U.X 0 ≅ SheafOfModules.unit (completedAdicRing T d) :=
    HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (CompletedAdicModules T d))
  choose q hq using fun n ↦ quotientModuleIso_exists T d r a ha n
  let v (n : ℕ) : (L n).X 0 ≅ completedAdicFiniteModule T d n :=
    whiskerRightIso u (completedAdicFiniteModule T d n) ≪≫
      λ_ (completedAdicFiniteModule T d n)
  let z (n : ℕ) : (K n).X 0 ≅ E.obj (Q n) :=
    E.mapIso ((S n).extendXIso ComplexShape.embeddingDownNat (i := 0) rfl)
  have hK (n : ℕ) (i : ℤ) (hi : i ≠ 0) : IsZero ((K n).X i) := by
    apply E.map_isZero
    exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (Q n) i hi).of_iso
      (HomologicalComplex.Hom.isoApp
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat (Q n) 0 0 rfl) i)
  have hL (n : ℕ) (i : ℤ) (hi : i ≠ 0) : IsZero ((L n).X i) := by
    let : MonoidalPreadditive (CompletedAdicModules T d) :=
      SheafOfModules.cochainModulesPreadditive (completedAdicCommRing T d)
    exact (tensorRight (completedAdicFiniteModule T d n)).map_isZero
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
        (𝟙_ (CompletedAdicModules T d)) i hi)
  let eQ (n : ℕ) : K n ≅ L n :=
    concentratedIso (K n) (L n) (z n ≪≫ q n ≪≫ (v n).symm) (hK n) (hL n)
  refine ⟨u ≪≫ completedRegularUnitIso T d, eQ, ?_⟩
  intro n
  have heQ : E.map ((S n).extendXIso
        ComplexShape.embeddingDownNat (i := 0) rfl).inv ≫
      (eQ n).hom.f 0 ≫ (v n).hom = (q n).hom := by
    rw [concentratedIso_zero]
    change (z n).inv ≫ ((z n).hom ≫ (q n).hom ≫ (v n).inv) ≫ (v n).hom = _
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  apply (cancel_mono (v n).hom).1
  change (u.hom ≫ (completedRegularUnitIso T d).hom ≫
    E.map (ModuleCat.ofHom (I ^ (n + 1)).mkQ) ≫
      E.map ((S n).extendXIso ComplexShape.embeddingDownNat (i := 0) rfl).inv ≫
        (eQ n).hom.f 0) ≫ (v n).hom = _
  calc
    _ = u.hom ≫ (completedRegularUnitIso T d).hom ≫
        E.map (ModuleCat.ofHom (I ^ (n + 1)).mkQ) ≫ (q n).hom := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ u.hom ≫ (completedRegularUnitIso T d).hom ≫
          E.map (ModuleCat.ofHom (I ^ (n + 1)).mkQ) ≫ k) heQ
    _ = u.hom ≫ reconstructionQuotientUnit T d n := by
      exact congrArg (fun k ↦ u.hom ≫ k) (hq n)
    _ = (completedQuotientTensorUnit T d U n).f 0 ≫ (v n).hom := by
      symm
      change ((reconstructionOrdinaryUnit T d).app (U.X 0) ≫
        limit.π ((completedAdicOrdinaryTower T d).obj (U.X 0)) (op n)) ≫
        (u.hom ▷ completedAdicFiniteModule T d n ≫
          (λ_ (completedAdicFiniteModule T d n)).hom) = _
      have hunit : (reconstructionOrdinaryUnit T d).app (U.X 0) ≫
          limit.π ((completedAdicOrdinaryTower T d).obj (U.X 0)) (op n) =
          (ρ_ (U.X 0)).inv ≫ U.X 0 ◁ reconstructionQuotientUnit T d n :=
        (reconstructionOrdinaryUnit_exists T d).exists.choose_spec (U.X 0) n
      exact (congrArg (fun f ↦ f ≫ (u.hom ▷ completedAdicFiniteModule T d n ≫
        (λ_ (completedAdicFiniteModule T d n)).hom)) hunit).trans
          (quotientUnit_normalization u _ _)

end AlgebraicGeometry.Scheme
