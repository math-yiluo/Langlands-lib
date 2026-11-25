/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantRealizationDataSupplement
import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantComparisonIsIso

/-! # The finite-module tensor-to-completion comparison

Source: Stacks Project, more-algebra.tex, Tag 0912; sites-modules.tex,
Tags 093J--093M. Only the comparison is asserted here, not exactness or local lissity.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The tensor-to-limit comparison for finite completion modules, with its two
projection identities.
Source: Stacks Project, more-algebra.tex, Tag 0912 (lemma-limit-flat), and
sites-modules.tex, Tags 093J--093M.
(blueprint: lem-weil-pbc-completed-constant-finite-module-comparison).

Proof: construct the finite projections for every completion module by sheafifying
the evaluation-semilinear residue map and using the scalar-extension adjunction. They
commute with the successor transitions, so the limit universal property gives a fixed
comparison map. The invertibility step is `completedConstantComparisonMap_isIso`;
apply it to a finite module and take `asIso` of that map. The composite with each
limit projection is exactly the constructed finite projection. Its proved linearity
formula gives the first assertion. Its proved naturality for C-linear maps gives
the second. The quotient maps, pure-tensor formulas, transition compatibility and
these two identities were constructed independently of the remaining invertibility
step, and do not require N to be finite. The residual invertibility argument is the
finite-presentation tensor-limit calculation of Tags 0912 and 093J--093M. -/
theorem completed_constant_finite_module_comparison (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I)
    (hφ : ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem X I) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom)) :
    ∃ e : ∀ (N : ModuleCat.{u + 1} (AdicCompletion I A))
        (_hN : Module.Finite (AdicCompletion I A) N),
      (SheafOfModules.restrictScalars ((adicLisseForget X).map
        (completedConstantBaseMap X I φ))).obj
          ((completedConstantRealization X I φ).obj N) ≅
        adicLisseCompletedModule X I (completedConstantUnderlyingModule I N),
      (∀ (N : ModuleCat.{u + 1} (AdicCompletion I A))
          (hN : Module.Finite (AdicCompletion I A) N) (n : ℕ) (U : X.ProEtᵒᵖ)
          (r : ((adicLisseCompletedRing X I).obj.obj U))
          (a : (adicLisseConstantRing X A).obj.obj U)
          (x : ((completedConstantRealization X I φ).obj N).val.obj U),
        ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))).hom.app U a =
            (limit.π (adicLisseRingSystem X I) (op n)).hom.app U r →
        (limit.π (adicLisseModuleSystem X I (completedConstantUnderlyingModule I N))
          (op n)).val.app U ((e N hN).hom.val.app U (r • x)) =
          a • (limit.π (adicLisseModuleSystem X I (completedConstantUnderlyingModule I N))
            (op n)).val.app U ((e N hN).hom.val.app U x)) ∧
      (∀ (M N : ModuleCat.{u + 1} (AdicCompletion I A))
          (hM : Module.Finite (AdicCompletion I A) M)
          (hN : Module.Finite (AdicCompletion I A) N) (f : M ⟶ N) (n : ℕ)
          (U : X.ProEtᵒᵖ) (x : ((completedConstantRealization X I φ).obj M).val.obj U),
        (limit.π (adicLisseModuleSystem X I (completedConstantUnderlyingModule I N))
            (op n)).val.app U ((e N hN).hom.val.app U
              (((completedConstantRealization X I φ).map f).val.app U x)) =
          (((adicLisseConstantModules X A).map (completedConstantQuotientMap I
            ((ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).map f)
              n)).val.app U)
            ((limit.π (adicLisseModuleSystem X I (completedConstantUnderlyingModule I M))
              (op n)).val.app U ((e M hM).hom.val.app U x))) := by
  let e (N : ModuleCat.{u + 1} (AdicCompletion I A))
      (hN : Module.Finite (AdicCompletion I A) N) :
      (SheafOfModules.restrictScalars ((adicLisseForget X).map
        (completedConstantBaseMap X I φ))).obj
          ((completedConstantRealization X I φ).obj N) ≅
        adicLisseCompletedModule X I (completedConstantUnderlyingModule I N) := by
    have := completedConstantComparisonMap_isIso X I φ hφ N hN
    exact asIso (completedConstantComparisonMap X I φ hφ N)
  have hp (N : ModuleCat.{u + 1} (AdicCompletion I A))
      (hN : Module.Finite (AdicCompletion I A) N) (n : ℕ) (U : X.ProEtᵒᵖ)
      (x : ((completedConstantRealization X I φ).obj N).val.obj U) :
      (limit.π (adicLisseModuleSystem X I (completedConstantUnderlyingModule I N))
        (op n)).val.app U ((e N hN).hom.val.app U x) =
      (completedConstantProjection X I φ hφ N n).val.app U x :=
    congrArg (fun k ↦ k.val.app U x) (completedConstantComparisonMap_π X I φ hφ N n)
  refine ⟨e, ?_, ?_⟩
  · intro N hN n U r a x ha
    rw [hp N hN, hp N hN]
    exact (completedConstantProjection_spec X I φ hφ N n).2 U r a x ha
  · intro M N hM hN f n U x
    rw [hp N hN, hp M hM]
    exact congrArg (fun k ↦ k.val.app U x)
      (completedConstantProjection_naturality X I φ hφ f n)

end AlgebraicGeometry.Scheme
