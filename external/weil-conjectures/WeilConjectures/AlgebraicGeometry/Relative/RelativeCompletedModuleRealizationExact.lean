/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantRealizationDataSupplement
import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantModuleModel
import WeilConjectures.AlgebraicGeometry.Adic.AdicLisseRelativeRestriction
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
import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.AdicCompletion.Completeness

/-! # Exact relative realization of completion modules

## References

* Stacks Project, Modules on Sites, Tags 093J--093M
* Pro-etale Cohomology, Tags 09BT and 09BV
* Stacks, Tags 093J--093M
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 1024

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem completedConstant_eval_step
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) (n : ℕ) :
    (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 2)).toRingHom) ≫
        CommRingCat.ofHom (Ideal.Quotient.factorPowSucc I (n + 1)) =
      CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom := by
  ext x
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective I A x
  change Ideal.Quotient.factorPowSucc I (n + 1)
    (AdicCompletion.evalₐ I (n + 2) (AdicCompletion.mk I A s)) =
      AdicCompletion.evalₐ I (n + 1) (AdicCompletion.mk I A s)
  simp only [AdicCompletion.evalₐ_mk]
  change Ideal.Quotient.mk _ (s.val (n + 2)) = Ideal.Quotient.mk _ (s.val (n + 1))
  apply Ideal.Quotient.eq.mpr
  have hs := (Submodule.Quotient.eq _).mp
    (AdicCompletion.AdicCauchySequence.mk_eq_mk (Nat.le_succ (n + 1)) s)
  simpa [smul_eq_mul, Ideal.mul_top] using hs

private theorem completedConstant_scalar_exists
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (I : Ideal A) :
    ∃ φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I,
      ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem X I) (op n) =
        (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom) := by
  let c := constantSheaf (ProEt.topology X) CommRingCat.{u + 1}
  let π : (Functor.const ℕᵒᵖ).obj (adicLisseConstantRing X (AdicCompletion I A)) ⟶
      adicLisseRingSystem X I := NatTrans.ofOpSequence
    (fun n ↦ c.map (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom))
    (fun n ↦ by
      simp only [Functor.const_obj_map, adicLisseRingSystem,
        Functor.ofOpSequence_map_homOfLE_succ]
      exact (congrArg c.map (completedConstant_eval_step I n)).symm.trans
        (c.map_comp _ _))
  exact ⟨limit.lift _ ⟨_, π⟩, fun n ↦ limit.lift_π _ _⟩

private theorem completedConstant_pullback_iso
    (X T : Scheme.{u}) (f : X ⟶ T) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (hfinite : ∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))) :
    ∃ β : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
        (adicLisseCompletedRing T I) ⟶ adicLisseCompletedRing X I,
      IsIso β ∧ ∀ n : ℕ, β ≫ limit.π (adicLisseRingSystem X I) (op n) =
        (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
          (limit.π (adicLisseRingSystem T I) (op n)) ≫
            proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
              (CommRingCat.of (A ⧸ I ^ (n + 1))) := by
  let Q : ℕᵒᵖ ⥤ CommRingCat.{u + 1} := Functor.ofOpSequence
    (X := fun n ↦ CommRingCat.of (A ⧸ I ^ (n + 1)))
    (fun n ↦ CommRingCat.ofHom (Ideal.Quotient.factorPowSucc I (n + 1)))
  let e (Z : Scheme.{u}) : adicLisseRingSystem Z I ≅ proEtaleCoefficientTower Z Q := by
    let a : adicLisseRingSystem Z I ⟶ proEtaleCoefficientTower Z Q :=
      NatTrans.ofOpSequence (fun n ↦ 𝟙 _) (fun n ↦ by
        simp [adicLisseRingSystem, proEtaleCoefficientTower, Q])
    have (n : ℕᵒᵖ) : IsIso (a.app n) := inferInstanceAs (IsIso (𝟙 _))
    have : IsIso a := NatIso.isIso_of_isIso_app a
    exact asIso a
  have (n : ℕᵒᵖ) : Finite (Q.obj n) := hfinite n.unop
  have : IsIso (proEtaleProfiniteComparison f Q) :=
    (proEtale_profinite_coefficient_inverse_image Q).2.1 X T f
  let F := proEtaleSheafInverseImage f CommRingCat.{u + 1}
  let β := F.map (lim.mapIso (e T)).hom ≫ proEtaleProfiniteComparison f Q ≫
    (lim.mapIso (e X)).inv
  refine ⟨β, inferInstance, ?_⟩
  intro n
  dsimp only [β]
  simp only [Category.assoc, Functor.mapIso_inv]
  change F.map (lim.mapIso (e T)).hom ≫ proEtaleProfiniteComparison f Q ≫
    limMap (e X).inv ≫ limit.π (adicLisseRingSystem X I) (op n) = _
  rw [limMap_π]
  rw [← Category.assoc (proEtaleProfiniteComparison f Q)]
  rw [(proEtale_profinite_coefficient_inverse_image Q).2.2.1 X T f (op n)]
  have hinv : (e X).inv.app (op n) = 𝟙 _ := by
    simp [e]
    rfl
  simp only [hinv, Category.comp_id]
  change F.map (limMap (e T).hom) ≫
    F.map (limit.π (proEtaleCoefficientTower T Q) (op n)) ≫
      proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
        (CommRingCat.of (A ⧸ I ^ (n + 1))) = _
  rw [← Category.assoc, ← F.map_comp, limMap_π]
  have hhom : (e T).hom.app (op n) = 𝟙 _ := rfl
  rw [hhom, Category.comp_id]

private theorem constant_exact (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    PreservesFiniteLimits (adicLisseConstantModules T A) ∧
      PreservesFiniteColimits (adicLisseConstantModules T A) := by
  let P : ModuleCat.{u + 1} A ⥤
      _root_.PresheafOfModules.{u + 1} ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of A)) :=
    siteConstantModulePresheaf (C := Discrete (ULift.{u + 1} Unit)) A ⋙
      PresheafOfModules.pushforward₀
        ((Functor.const T.ProEt).obj (Discrete.mk (ULift.up ())))
        ((Functor.const (Discrete (ULift.{u + 1} Unit))ᵒᵖ).obj (RingCat.of A))
  have : PreservesFiniteLimits P := by
    constructor
    intro K _ _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun X ↦ hc)⟩
  have : PreservesFiniteColimits P := by
    constructor
    intro K _ _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun X ↦ hc)⟩
  exact ⟨comp_preservesFiniteLimits P
    (PresheafOfModules.sheafification (adicLisseConstantUnit T A)),
    comp_preservesFiniteColimits P
      (PresheafOfModules.sheafification (adicLisseConstantUnit T A))⟩

private theorem completion_eval_kernel
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ I n).toRingHom =
      (I.map (algebraMap A (AdicCompletion I A))) ^ n := by
  ext x
  trans x ∈ (AdicCompletion.eval I A n).ker
  · have he : (I ^ n • ⊤ : Ideal A) = I ^ n := by simp
    have hi : Function.Injective (Ideal.Quotient.factor (le_of_eq he.symm)) := by
      simp [RingHom.injective_iff_ker_eq_bot, Ideal.Quotient.factor_ker]
    change AdicCompletion.evalₐ I n x = 0 ↔ AdicCompletion.eval I A n x = 0
    rw [← AdicCompletion.factor_evalₐ_eq_eval I x (le_of_eq he.symm)]
    exact (map_eq_zero_iff (Ideal.Quotient.factor (le_of_eq he.symm)) hi).symm
  · simp [← AdicCompletion.pow_smul_top_eq_ker_eval (I := I) (M := A)
      I.fg_of_isNoetherianRing, ← Ideal.map_pow]

private noncomputable def completion_quotient_iso
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    CommRingCat.of (AdicCompletion I A ⧸
      (I.map (algebraMap A (AdicCompletion I A))) ^ n) ≅
        CommRingCat.of (A ⧸ I ^ n) :=
  ((Ideal.quotientEquivAlgOfEq (AdicCompletion I A)
    (completion_eval_kernel I n).symm).toRingEquiv.trans
      ((AdicCompletion.evalₐ I n).toRingHom.quotientKerEquivOfSurjective
        (AdicCompletion.surjective_evalₐ I n))).toCommRingCatIso

private theorem completion_quotient_iso_mk
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (n : ℕ)
    (x : AdicCompletion I A) :
    (completion_quotient_iso I n).hom (Ideal.Quotient.mk _ x) =
      AdicCompletion.evalₐ I n x := by
  simp [completion_quotient_iso]

private noncomputable def completion_system_iso (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    adicLisseRingSystem X (I.map (algebraMap A (AdicCompletion I A))) ≅
      adicLisseRingSystem X I := by
  let c := constantSheaf (ProEt.topology X) CommRingCat.{u + 1}
  let q := fun n ↦ c.mapIso (completion_quotient_iso I (n + 1))
  let a := NatTrans.ofOpSequence (F := adicLisseRingSystem X
    (I.map (algebraMap A (AdicCompletion I A)))) (G := adicLisseRingSystem X I)
    (fun n ↦ (q n).hom) (fun n ↦ by
      simp only [adicLisseRingSystem, Functor.ofOpSequence_map_homOfLE_succ]
      change c.map _ ≫ c.map _ = c.map _ ≫ c.map _
      rw [← c.map_comp, ← c.map_comp]
      congr 1
      ext x
      change (completion_quotient_iso I (n + 1)).hom (Ideal.Quotient.mk _ x) =
        Ideal.Quotient.factorPowSucc I (n + 1)
          ((completion_quotient_iso I (n + 2)).hom (Ideal.Quotient.mk _ x))
      rw [completion_quotient_iso_mk, completion_quotient_iso_mk]
      exact (ConcreteCategory.congr_hom (completedConstant_eval_step I n) x).symm)
  have (n : ℕᵒᵖ) : IsIso (a.app n) := inferInstanceAs (IsIso (q n.unop).hom)
  have : IsIso a := NatIso.isIso_of_isIso_app a
  exact asIso a

private theorem completedRealization_exact (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I)
    (hφ : ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem X I) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom)) :
    PreservesFiniteLimits (completedConstantRealization X I φ) ∧
      PreservesFiniteColimits (completedConstantRealization X I φ) := by
  let := AdicCompletion.isNoetherianRing I
  let J := I.map (algebraMap A (AdicCompletion I A))
  let e : adicLisseCompletedRing X J ≅ adicLisseCompletedRing X I :=
    lim.mapIso (completion_system_iso X I)
  have hp (n : ℕ) : φ ≫ e.inv ≫ limit.π (adicLisseRingSystem X J) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ (n + 1)))) := by
    let q : adicLisseConstantRing X (AdicCompletion I A ⧸ J ^ (n + 1)) ≅
        adicLisseConstantRing X (A ⧸ I ^ (n + 1)) :=
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).mapIso
        (completion_quotient_iso.{u} I (n + 1))
    apply (cancel_mono q.hom).1
    change (φ ≫ limMap (completion_system_iso X I).inv ≫
      limit.π (adicLisseRingSystem X J) (op n)) ≫ _ = _
    rw [Category.assoc, limMap_π]
    simp only [Category.assoc]
    have hi : (completion_system_iso X I).inv.app (op n) ≫
        (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
          (completion_quotient_iso I (n + 1)).hom = 𝟙 _ :=
      (completion_system_iso X I).inv_hom_id_app (op n)
    dsimp only [q, Functor.mapIso_hom]
    erw [hi, Category.comp_id, hφ, ← Functor.map_comp]
    congr 1
  have he : PreservesFiniteLimits (completedAdicChange X φ) ∧
      PreservesFiniteColimits (completedAdicChange X φ) :=
    (exactFunctor_iff (completedAdicChange X φ)).1
      (completed_constant_algebra_flat_quotients.{u} X J _ e φ hp).2.1
  have : PreservesFiniteLimits (completedConstantExtension X φ) := he.1
  have : PreservesFiniteColimits (completedConstantExtension X φ) := he.2
  have := (constant_exact X (AdicCompletion I A)).1
  have := (constant_exact X (AdicCompletion I A)).2
  exact ⟨comp_preservesFiniteLimits _ _, comp_preservesFiniteColimits _ _⟩

private noncomputable def restrictScalars_idIso (Y : Scheme.{u})
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    pbcRestrict (𝟙 R) ≅ 𝟭 (pbcModules Y R) :=
  NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk
        (fun U ↦ (ModuleCat.restrictScalarsId (R.obj.obj U)).app (M.val.obj U))
        (fun {_ _} _ ↦ by ext x; rfl))) (fun _ ↦ by ext U x; rfl)

private theorem lisseLocalModel_of_iso (Y : Scheme.{u})
    (R₀ Rhat : Sheaf (ProEt.topology Y) RingCat.{u + 1})
    (Rₙ : ℕ → Sheaf (ProEt.topology Y) RingCat.{u + 1})
    (ρ : ∀ n : ℕ, R₀ ⟶ Rₙ n) (π : ∀ n : ℕ, Rhat ⟶ Rₙ n)
    (S : ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} R₀)
    {F G : ringedSiteModules.{u + 1} Rhat} (e : F ≅ G) (V : Y.ProEt)
    (hG : IsAdicLisseLocalModel Y R₀ Rhat Rₙ ρ π S G V) :
    IsAdicLisseLocalModel Y R₀ Rhat Rₙ ρ π S F V := by
  obtain ⟨em, hlin⟩ := hG
  refine ⟨((ProEt.topology Y).overPullback AddCommGrpCat.{u + 1} V).mapIso
    ((SheafOfModules.toSheaf Rhat).mapIso e) ≪≫ em, ?_⟩
  intro n W r a x ha
  change (limit.π S (op n)).val.app (op W.unop.left)
    (em.hom.hom.app W ((e.hom.val.app _).hom (r • x))) =
      a • (limit.π S (op n)).val.app (op W.unop.left)
        (em.hom.hom.app W ((e.hom.val.app _).hom x))
  rw [(e.hom.val.app _).hom.map_smul]
  exact hlin n W r a ((e.hom.val.app _).hom x) ha

private theorem relativelyLisse_of_iso {X Y : Scheme.{u}} (h : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {F G : pbcModules Y ((adicTowerInverseImage h).obj (adicLisseCompletedRing X I))}
    (e : F ≅ G) (hG : IsRelativelyAdicLisseModule h I G) :
    IsRelativelyAdicLisseModule h I F := by
  obtain ⟨T, hT, hmodel⟩ := hG
  refine ⟨T, hT, ?_⟩
  intro V f hf
  obtain ⟨N, hN, hfin, hlocal⟩ := hmodel V f hf
  exact ⟨N, hN, hfin, lisseLocalModel_of_iso Y _ _ _ _ _ _ e V hlocal⟩

-- The original statement names an intentionally unused existential additivity witness.
set_option linter.unusedVariables false in
/-- The specified completion scalar maps give an exact relative module realization.
Finite completion modules become relatively adic-lisse modules. -/
theorem relative_completed_module_realization_exact
    (X Y : Scheme.{u}) (h : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    ∃ φ : adicLisseConstantRing Y (AdicCompletion d.ideal A) ⟶
      adicLisseCompletedRing Y d.ideal,
      (∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem Y d.ideal) (op n) =
      (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ d.ideal (n + 1)).toRingHom)) ∧
      ∃ β : (adicTowerInverseImage h).obj (adicLisseCompletedRing X d.ideal) ⟶
      adicLisseCompletedRing Y d.ideal,
        (∀ n : ℕ, β ≫ limit.π (adicLisseRingSystem Y d.ideal) (op n) =
      (adicTowerInverseImage h).map (limit.π (adicLisseRingSystem X d.ideal) (op n)) ≫
        proEtaleConstantInverseImageMap h CommRingCat.{u + 1}
          (CommRingCat.of (A ⧸ d.ideal ^ (n + 1)))) ∧
        let c := completedConstantRealization Y d.ideal φ ⋙ pbcRestrict β ⋙
      pbcRestrict ((adicTowerInverseImage h).map (pbcCompletedComparison X d).inv)
        ∃ hc : c.Additive,
          PreservesFiniteLimits c ∧ PreservesFiniteColimits c ∧
          ∀ N : ModuleCat.{u + 1} (AdicCompletion d.ideal A),
            Module.Finite (AdicCompletion d.ideal A) N →
              @IsRelativelyAdicLisseModule _ _ h A _ d.noetherian d.ideal
                ((pbcRestrict ((adicTowerInverseImage h).map
                  (pbcCompletedComparison X d).hom)).obj (c.obj N))  := by
  let := d.noetherian
  obtain ⟨φ, hφ⟩ := completedConstant_scalar_exists Y d.ideal
  obtain ⟨β, hβiso, hβ⟩ := completedConstant_pullback_iso Y X h d.ideal d.quotientFinite
  obtain ⟨m, hm⟩ := completed_constant_module_model Y d.ideal φ hφ
  subst φ
  refine ⟨m.scalar, hφ, β, hβ, ?_⟩
  let := m.additive
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · have := (completedRealization_exact Y d.ideal m.scalar hφ).1
    exact comp_preservesFiniteLimits _ _
  · have := (completedRealization_exact Y d.ideal m.scalar hφ).2
    exact comp_preservesFiniteColimits _ _
  · intro N hN
    let F := (completedConstantRealization Y d.ideal m.scalar).obj N
    have hl : IsRelativelyAdicLisseModule h d.ideal ((pbcRestrict β).obj F) :=
      adicLisse_relative_restrict h d.ideal β hβ F (m.lisse N hN)
    let a := (adicTowerInverseImage h).map (pbcCompletedComparison X d).inv
    let b := (adicTowerInverseImage h).map (pbcCompletedComparison X d).hom
    have hba : b ≫ a = 𝟙 _ := by
      rw [← (adicTowerInverseImage h).map_comp, Iso.hom_inv_id]
      exact (adicTowerInverseImage h).map_id _
    let e := (pbcRestrictComp b a (𝟙 _) hba).app ((pbcRestrict β).obj F) ≪≫
      (restrictScalars_idIso Y _).app ((pbcRestrict β).obj F)
    exact relativelyLisse_of_iso h d.ideal e hl

end AlgebraicGeometry.Scheme
