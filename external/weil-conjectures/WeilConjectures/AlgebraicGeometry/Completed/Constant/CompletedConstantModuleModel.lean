/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantRealizationDataSupplement
import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantFiniteModuleComparison
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
import all WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.FiniteModuleComplete
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Module.Torsion.Basic

/-! # Tensor realization of finite completion modules

Source: Stacks Tags 0912, 093J--093M and 09BT.
(blueprint: lem-weil-pbc-completed-constant-module-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private theorem completion_eval_kernel
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ I n).toRingHom =
      (I.map (algebraMap A (AdicCompletion I A))) ^ n := by
  apply Submodule.restrictScalars_injective A
  rw [← Ideal.map_pow, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval (IsNoetherian.noetherian I)]
  ext x
  change AdicCompletion.evalₐ I n x = 0 ↔ AdicCompletion.eval I A n x = 0
  have h : (I ^ n • ⊤ : Ideal A) = I ^ n := by simp
  change Ideal.quotientEquivAlgOfEq A h (AdicCompletion.eval I A n x) = 0 ↔ _
  exact map_eq_zero_iff _ (Ideal.quotientEquivAlgOfEq A h).injective

private def completion_quotient_iso
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    CommRingCat.of ((AdicCompletion I A) ⧸
      (I.map (algebraMap A (AdicCompletion I A))) ^ n) ≅ CommRingCat.of (A ⧸ I ^ n) :=
  (Ideal.quotientEquivAlgOfEq (AdicCompletion I A)
    (completion_eval_kernel I n).symm).toRingEquiv.toCommRingCatIso ≪≫
      ((AdicCompletion.evalₐ I n).toRingHom.quotientKerEquivOfSurjective
        (AdicCompletion.surjective_evalₐ I n)).toCommRingCatIso

private theorem completion_quotient_iso_mk
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    CommRingCat.ofHom (Ideal.Quotient.mk
      ((I.map (algebraMap A (AdicCompletion I A))) ^ n)) ≫
        (completion_quotient_iso I n).hom =
      CommRingCat.ofHom (AdicCompletion.evalₐ I n).toRingHom := by
  ext x
  exact RingHom.quotientKerEquivOfSurjective_apply_mk
    (AdicCompletion.surjective_evalₐ I n) x

private theorem completion_eval_step
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) (n : ℕ) :
    CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 2)).toRingHom ≫
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

private theorem completion_quotient_iso_step
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    CommRingCat.ofHom (Ideal.Quotient.factorPowSucc
        (I.map (algebraMap A (AdicCompletion I A))) (n + 1)) ≫
        (completion_quotient_iso I (n + 1)).hom =
      (completion_quotient_iso I (n + 2)).hom ≫
        CommRingCat.ofHom (Ideal.Quotient.factorPowSucc I (n + 1)) := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  have h (k : ℕ) : (completion_quotient_iso I k).hom.hom
      (Ideal.Quotient.mk _ x) = AdicCompletion.evalₐ I k x :=
    ConcreteCategory.congr_hom (completion_quotient_iso_mk I k) x
  change (completion_quotient_iso I (n + 1)).hom.hom
      (Ideal.Quotient.mk _ x) =
    Ideal.Quotient.factorPowSucc I (n + 1)
      ((completion_quotient_iso I (n + 2)).hom.hom (Ideal.Quotient.mk _ x))
  exact (h (n + 1)).trans ((ConcreteCategory.congr_hom
    (completion_eval_step I n) x).symm.trans
      (congrArg (Ideal.Quotient.factorPowSucc I (n + 1)) (h (n + 2)).symm))

private def completion_tower_iso (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    adicLisseRingSystem X (I.map (algebraMap A (AdicCompletion I A))) ≅
      adicLisseRingSystem X I := by
  let c := constantSheaf (ProEt.topology X) CommRingCat.{u + 1}
  let e (n : ℕ) := c.mapIso (completion_quotient_iso I (n + 1))
  refine NatIso.ofComponents (fun n ↦ e n.unop) ?_
  intro n m f
  let h : adicLisseRingSystem X (I.map (algebraMap A (AdicCompletion I A))) ⟶
      adicLisseRingSystem X I :=
    NatTrans.ofOpSequence (fun n ↦ (e n).hom) (fun n ↦ by
      change (adicLisseRingSystem X (I.map (algebraMap A (AdicCompletion I A)))).map
        (homOfLE (Nat.le_succ n)).op ≫ (e n).hom =
          (e (n + 1)).hom ≫ (adicLisseRingSystem X I).map
            (homOfLE (Nat.le_succ n)).op
      simpa only [adicLisseRingSystem, Functor.ofOpSequence_map_homOfLE_succ,
        e, Functor.mapIso_hom, c, Functor.map_comp] using
          congrArg c.map (completion_quotient_iso_step I n))
  exact h.naturality f

private theorem completion_scalar_flat (X : Scheme.{u})
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
    lim.mapIso (completion_tower_iso X I)
  have hc (n : ℕ) : φ ≫ e.inv ≫ limit.π (adicLisseRingSystem X J) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ (n + 1)))) := by
    let q : adicLisseConstantRing X ((AdicCompletion I A) ⧸ J ^ (n + 1)) ≅
        adicLisseConstantRing X (A ⧸ I ^ (n + 1)) :=
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).mapIso
        (completion_quotient_iso I (n + 1))
    apply (cancel_mono q.hom).1
    change (φ ≫ e.inv ≫ limit.π (adicLisseRingSystem X J) (op n)) ≫
        (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
          (completion_quotient_iso I (n + 1)).hom =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ (n + 1)))) ≫
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (completion_quotient_iso I (n + 1)).hom
    have he : e.inv ≫ limit.π (adicLisseRingSystem X J) (op n) ≫
        (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
          (completion_quotient_iso I (n + 1)).hom =
        limit.π (adicLisseRingSystem X I) (op n) := by
      change e.inv ≫ limit.π (adicLisseRingSystem X J) (op n) ≫
        (completion_tower_iso X I).hom.app (op n) = _
      rw [← limMap_π]
      change e.inv ≫ e.hom ≫ _ = _
      rw [← Category.assoc, e.inv_hom_id, Category.id_comp]
    simp only [Category.assoc]
    rw [he, hφ, ← Functor.map_comp, completion_quotient_iso_mk]
  have he := (completed_constant_algebra_flat_quotients X J _ e φ hc).2.1
  have : PreservesFiniteLimits (completedConstantExtension X φ) := he.1
  have : PreservesFiniteColimits (completedConstantExtension X φ) := he.2
  have := (CompletedConstantReduction.constant_exact X (AdicCompletion I A)).1
  have := (CompletedConstantReduction.constant_exact X (AdicCompletion I A)).2
  exact ⟨comp_preservesFiniteLimits _ _, comp_preservesFiniteColimits _ _⟩

private theorem completion_module_properties
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (N : ModuleCat.{u + 1} (AdicCompletion I A))
    (hN : Module.Finite (AdicCompletion I A) N) :
    IsAdicComplete I (completedConstantUnderlyingModule I N) ∧
      Module.Finite A ((completedConstantUnderlyingModule I N) ⧸
        (I • ⊤ : Submodule A (completedConstantUnderlyingModule I N))) := by
  let C := AdicCompletion I A
  let J := I.map (algebraMap A C)
  let M := completedConstantUnderlyingModule I N
  let : Module C M := inferInstanceAs (Module C N)
  let : IsScalarTower A C M := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  let : Module.Finite C M := hN
  let : IsNoetherianRing C := AdicCompletion.isNoetherianRing I
  let : IsAdicComplete J C := AdicCompletion.isAdicComplete_self I
    (IsNoetherian.noetherian I)
  have hcomplete : IsAdicComplete J M :=
    finite_module_complete_over_complete_noetherian C J M
  refine ⟨(IsAdicComplete.map_algebraMap_iff I M).1 hcomplete, ?_⟩
  have hs : Function.Surjective (algebraMap A (C ⧸ J)) := by
    intro z
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I 1 c)
    refine ⟨a, ?_⟩
    change Ideal.Quotient.mk J (algebraMap A C a) = Ideal.Quotient.mk J c
    apply Ideal.Quotient.eq.mpr
    rw [← pow_one J, ← completion_eval_kernel I 1]
    change AdicCompletion.evalₐ I 1 (algebraMap A C a - c) = 0
    rw [map_sub]
    change AdicCompletion.evalₐ I 1 (AdicCompletion.of I A a) - _ = 0
    rw [AdicCompletion.evalₐ_of, ha, sub_self]
  let : Module.Finite A (C ⧸ J) := (RingHom.Finite.of_surjective _ hs)
  let P : Submodule C M := J • ⊤
  have hp : P.restrictScalars A = I • (⊤ : Submodule A M) :=
    Ideal.smul_restrictScalars I (⊤ : Submodule C M)
  let : Module.Finite A (M ⧸ P) := Module.Finite.trans (C ⧸ J) (M ⧸ P)
  exact Module.Finite.equiv ((Submodule.Quotient.restrictScalarsEquiv A P).symm.trans
    (Submodule.quotEquivOfEq _ _ hp))

/-- Scalar extension realizes the compatible finite quotient module model.
Source: Stacks Tag 0912 (lemma-limit-flat), Tags 093J--093M and Tag 09BT, clause (3).
(blueprint: lem-weil-pbc-completed-constant-module-model).

Proof: put C = AdicCompletion I A and J = I C. Completion is Noetherian and J-complete,
and evaluation identifies C/J^(n+1) with A/I^(n+1). A finite C-module N is complete and
finitely presented. Its reduction modulo J is finite as a module over C/J = A/I.
On a site object U, the constant sections of C/J^(n+1) are flat over that quotient;
their transition maps are surjective. The limit-flat tensor theorem identifies
N tensor_C H(U) with the limit of the constant quotient-module sections. The
finitely presented constant-section tensor comparison identifies this with the
sections of H tensor_(constant C) constant N. These comparisons are natural in U
and N, and send a tensor to its projected scalar times the residue of N.
Consequently they sheafify to the specified realization isomorphisms; the same
formula gives their linearity and naturality. H is flat over constant C by 093M
applied to (C,J), so the exact constant functor followed by scalar extension is
exact. Restricting to finite modules preserves their finite limits and colimits.
Finally N, restricted to A, is I-complete; its quotient by I is finite over A/I.
Use the maximal covering sieve and the realization isomorphism on every object
for the adic-lisse local model. The projected tensor formula gives its scalar law.
The argument includes the zero ring, I = 0, I = top, and N = 0. -/
theorem completed_constant_module_model (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I)
    (hφ : ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem X I) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom)) :
    ∃ d : CompletedConstantModuleRealization X I, d.scalar = φ := by
  obtain ⟨e, hlinear, hnatural⟩ := completed_constant_finite_module_comparison X I φ hφ
  have hflat := completion_scalar_flat X I φ hφ
  let : PreservesFiniteLimits (completedConstantRealization X I φ) := hflat.1
  let : PreservesFiniteColimits (completedConstantRealization X I φ) := hflat.2
  let : IsNoetherianRing (AdicCompletion I A) := AdicCompletion.isNoetherianRing I
  let : PreservesFiniteLimits (completedConstantFiniteModules (AdicCompletion I A)).ι :=
    inferInstanceAs (PreservesFiniteLimits (forget₂
      (FGModuleCat.{u + 1} (AdicCompletion I A)) (ModuleCat.{u + 1} (AdicCompletion I A))))
  let : PreservesFiniteColimits (completedConstantFiniteModules (AdicCompletion I A)).ι :=
    inferInstanceAs (PreservesFiniteColimits (forget₂
      (FGModuleCat.{u + 1} (AdicCompletion I A)) (ModuleCat.{u + 1} (AdicCompletion I A))))
  let : (adicLisseConstantModules X (AdicCompletion I A)).Additive :=
    CompletedConstantReduction.constant_additive X _
  refine ⟨{ scalar := φ
            scalar_projection := hφ
            additive := by
              dsimp only [completedConstantRealization]
              infer_instance
            exact_finite := ⟨inferInstance, inferInstance⟩
            lisse := ?_
            realization := e
            linearity := hlinear
            naturality := hnatural }, rfl⟩
  intro N hN
  obtain ⟨hc, hf⟩ := completion_module_properties I N hN
  refine ⟨⊤, (ProEt.topology X).top_mem _, ?_⟩
  intro V f _
  refine ⟨completedConstantUnderlyingModule I N, hc, hf, ?_⟩
  refine ⟨((ProEt.topology X).overPullback AddCommGrpCat.{u + 1} V).mapIso
    ((SheafOfModules.toSheaf (adicLisseRing X A)).mapIso (e N hN)), ?_⟩
  intro n W r a x ha
  exact hlinear N hN n (op W.unop.left) r a x ha

end AlgebraicGeometry.Scheme
