/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantFiniteProjection
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
/-! # Compatibility and limit lift of completed constant projections

Source: Stacks Project, Modules on Sites, Tags 03EK and 093J--093M.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] completedConstantProjection

namespace CompletedConstantProjection

private theorem quotientMap_residueMul (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    {M N : ModuleCat.{u + 1} (AdicCompletion I A)} (f : M ⟶ N)
    (n : ℕ) (U : X.ProEtᵒᵖ)
    (r : (adicLisseConstantRing X (A ⧸ I ^ (n + 1))).obj.obj U)
    (y : ((adicLisseModuleSystem X I (completedConstantUnderlyingModule I M)).obj
      (op n)).val.obj U) :
    ((adicLisseConstantModules X A).map (completedConstantQuotientMap I
      ((ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).map f) n)).val.app U
        (completedConstantResidueMul X I M n U r y) =
      completedConstantResidueMul X I N n U r
        (((adicLisseConstantModules X A).map (completedConstantQuotientMap I
          ((ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).map f) n)).val.app U
            y) := by
  let fA := (ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).map f
  let g := fA.hom.reduceModIdeal (I ^ (n + 1))
  exact (((adicLisseConstantModules X (A ⧸ I ^ (n + 1))).map
    (ModuleCat.ofHom g)).val.app U).hom.map_smul r y

private theorem transition_residueMul (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (N : ModuleCat.{u + 1} (AdicCompletion I A)) (n : ℕ) (U : X.ProEtᵒᵖ)
    (r : (adicLisseConstantRing X (A ⧸ I ^ (n + 2))).obj.obj U)
    (y : ((adicLisseModuleSystem X I (completedConstantUnderlyingModule I N)).obj
      (op (n + 1))).val.obj U) :
    ((adicLisseModuleSystem X I (completedConstantUnderlyingModule I N)).map
      (homOfLE (Nat.le_succ n)).op).val.app U
        (completedConstantResidueMul X I N (n + 1) U r y) =
      completedConstantResidueMul X I N n U
        (((adicLisseRingSystem X I).map (homOfLE (Nat.le_succ n)).op).hom.app U r)
        (((adicLisseModuleSystem X I (completedConstantUnderlyingModule I N)).map
          (homOfLE (Nat.le_succ n)).op).val.app U y) := by
  let f := Ideal.Quotient.factorPowSucc I (n + 1)
  let q : ModuleCat.of (A ⧸ I ^ (n + 2)) (completedConstantUnderlyingModule I N ⧸
      (I ^ (n + 2) • ⊤ : Submodule A (completedConstantUnderlyingModule I N))) →ₛₗ[f]
      ModuleCat.of (A ⧸ I ^ (n + 1)) (completedConstantUnderlyingModule I N ⧸
        (I ^ (n + 1) • ⊤ : Submodule A (completedConstantUnderlyingModule I N))) :=
    { toFun := Submodule.factorPowSucc I (completedConstantUnderlyingModule I N) (n + 1)
      map_add' := map_add _
      map_smul' := by
        intro r x
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
        induction x using Submodule.Quotient.induction_on with
        | _ x => rfl }
  let c := (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map (CommRingCat.ofHom f)
  let g := constantMap X f c (𝟙 _) (Category.comp_id c) _ _ q
  have hg := constantMap_underlying X f c (𝟙 _) (Category.comp_id c) _ _ q
  have hgu (z) : g.val.app U z =
      (((adicLisseConstantModules X A).map (ModuleCat.ofHom
        (Submodule.factorPowSucc I (completedConstantUnderlyingModule I N) (n + 1)))).val.app U
          z) := congrArg (fun k ↦ k.hom.app U z) hg
  have h : g.val.app U (completedConstantResidueMul X I N (n + 1) U r y) =
      completedConstantResidueMul X I N n U (c.hom.app U r) (g.val.app U y) :=
    (g.val.app U).hom.map_smul r y
  erw [hgu, hgu] at h
  simp only [adicLisseModuleSystem, adicLisseRingSystem,
    Functor.ofOpSequence_map_homOfLE_succ]
  with_unfolding_all exact h

end CompletedConstantProjection

/-- The constructed projections commute with C-linear module maps.
Source: Stacks Tags 03EK and 093J--093M
(blueprint: def-weil-pbc-completed-constant-projection-maps).
Proof: test on pure tensors of completed scalars and constant module elements. The source
map keeps the scalar and applies f to the element. The residue map of f is linear over
the quotient ring and sends the residue of x to the residue of f(x), so the two expressions
coincide. Tensor generation and the local surjectivity of the constant-sheafification unit
extend this identity to all sections. -/
theorem completedConstantProjection_naturality (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I)
    (hφ : ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem X I) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom))
    {M N : ModuleCat.{u + 1} (AdicCompletion I A)} (f : M ⟶ N) (n : ℕ) :
    (SheafOfModules.restrictScalars ((adicLisseForget X).map
      (completedConstantBaseMap X I φ))).map
        ((completedConstantRealization X I φ).map f) ≫
          completedConstantProjection X I φ hφ N n =
      completedConstantProjection X I φ hφ M n ≫
        (adicLisseConstantModules X A).map (completedConstantQuotientMap I
          ((ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).map f) n) := by
  apply CompletedConstantProjection.realization_hom_ext X φ
    (completedConstantBaseMap X I φ) M
  intro U r x
  dsimp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  change (completedConstantProjection X I φ hφ N n).val.app U
    (((completedAdicChange X φ).map ((adicLisseConstantModules X _).map f)).val.app U
      (completedAdicChangeTensor X φ ((adicLisseConstantModules X _).obj M) U r
        (completedConstantGenerator X _ M U x))) =
    (((adicLisseConstantModules X A).map (completedConstantQuotientMap I
      ((ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).map f) n)).val.app U)
        ((completedConstantProjection X I φ hφ M n).val.app U
          (completedAdicChangeTensor X φ ((adicLisseConstantModules X _).obj M) U r
            (completedConstantGenerator X _ M U x)))
  have hm : ((completedAdicChange X φ).map ((adicLisseConstantModules X _).map f)).val.app U
      (completedAdicChangeTensor X φ ((adicLisseConstantModules X _).obj M) U r
        (completedConstantGenerator X _ M U x)) =
      completedAdicChangeTensor X φ ((adicLisseConstantModules X _).obj N) U r
        (((adicLisseConstantModules X _).map f).val.app U
          (completedConstantGenerator X _ M U x)) :=
    reductionTensor_map X φ ((adicLisseConstantModules X _).map f) U r
      (completedConstantGenerator X _ M U x)
  erw [hm, CompletedConstantProjection.constant_map_generator]
  erw [(completedConstantProjection_spec X I φ hφ N n).1,
    (completedConstantProjection_spec X I φ hφ M n).1]
  rw [CompletedConstantProjection.quotientMap_residueMul,
    CompletedConstantProjection.constant_map_generator]
  rfl

/-- The finite projections commute with successor quotient transitions.
Source: Stacks Tags 03EK and 093J--093M
(blueprint: def-weil-pbc-completed-constant-projection-maps).
Proof: on a pure tensor the successor quotient sends the projected scalar to its preceding
projection, and sends the residue of x to its preceding residue. The ring limit identity
identifies the first factors. Local tensor generation gives equality of sheaf maps. -/
theorem completedConstantProjection_step (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I)
    (hφ : ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem X I) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom))
    (N : ModuleCat.{u + 1} (AdicCompletion I A)) (n : ℕ) :
    completedConstantProjection X I φ hφ N (n + 1) ≫
      (adicLisseModuleSystem X I (completedConstantUnderlyingModule I N)).map
        (homOfLE (Nat.le_succ n)).op =
      completedConstantProjection X I φ hφ N n := by
  apply CompletedConstantProjection.realization_hom_ext X φ
    (completedConstantBaseMap X I φ) N
  intro U r x
  change ((adicLisseModuleSystem X I (completedConstantUnderlyingModule I N)).map
    (homOfLE (Nat.le_succ n)).op).val.app U
      ((completedConstantProjection X I φ hφ N (n + 1)).val.app U
        (completedAdicChangeTensor X φ ((adicLisseConstantModules X _).obj N) U r
          (completedConstantGenerator X _ N U x))) = _
  erw [(completedConstantProjection_spec X I φ hφ N (n + 1)).1,
    (completedConstantProjection_spec X I φ hφ N n).1]
  rw [CompletedConstantProjection.transition_residueMul]
  have hp := congrArg (fun k ↦ k.hom.app U r)
    (limit.w (adicLisseRingSystem X I) (homOfLE (Nat.le_succ n)).op)
  change ((adicLisseRingSystem X I).map (homOfLE (Nat.le_succ n)).op).hom.app U
    ((limit.π (adicLisseRingSystem X I) (op (n + 1))).hom.app U r) =
      (limit.π (adicLisseRingSystem X I) (op n)).hom.app U r at hp
  rw [hp]
  congr 1
  simp only [adicLisseModuleSystem, Functor.ofOpSequence_map_homOfLE_succ]
  exact CompletedConstantProjection.constant_map_generator X
    (ModuleCat.ofHom (Submodule.factorPowSucc I (completedConstantUnderlyingModule I N)
      (n + 1))) U ((I ^ (n + 1 + 1) • ⊤ : Submodule A
        (completedConstantUnderlyingModule I N)).mkQ x)

/-- The actual compatible residue cone for tensor realization.
Source: Stacks Tags 03EK and 093J--093M
(blueprint: def-weil-pbc-completed-constant-projection-maps). -/
def completedConstantComparisonCone (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I)
    (hφ : ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem X I) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom))
    (N : ModuleCat.{u + 1} (AdicCompletion I A)) :
    Cone (adicLisseModuleSystem X I (completedConstantUnderlyingModule I N)) where
  pt := (SheafOfModules.restrictScalars ((adicLisseForget X).map
    (completedConstantBaseMap X I φ))).obj ((completedConstantRealization X I φ).obj N)
  π := NatTrans.ofOpSequence (completedConstantProjection X I φ hφ N) (by
    intro n
    change (𝟙 _) ≫ _ = _
    rw [Category.id_comp]
    exact (completedConstantProjection_step X I φ hφ N n).symm)

/-- The canonical tensor-to-limit map, before asserting invertibility.
Source: Stacks Tags 03EK and 093J--093M
(blueprint: def-weil-pbc-completed-constant-projection-maps). -/
def completedConstantComparisonMap (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I)
    (hφ : ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem X I) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom))
    (N : ModuleCat.{u + 1} (AdicCompletion I A)) :
    (SheafOfModules.restrictScalars ((adicLisseForget X).map
      (completedConstantBaseMap X I φ))).obj ((completedConstantRealization X I φ).obj N) ⟶
        adicLisseCompletedModule X I (completedConstantUnderlyingModule I N) :=
  limit.lift _ (completedConstantComparisonCone X I φ hφ N)

/-- Finite projections of the canonical limit map are the constructed residue maps.
Source: the limit universal property
(blueprint: def-weil-pbc-completed-constant-projection-maps). -/
theorem completedConstantComparisonMap_π (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I)
    (hφ : ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem X I) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom))
    (N : ModuleCat.{u + 1} (AdicCompletion I A)) (n : ℕ) :
    completedConstantComparisonMap X I φ hφ N ≫
      limit.π (adicLisseModuleSystem X I (completedConstantUnderlyingModule I N)) (op n) =
        completedConstantProjection X I φ hφ N n :=
  limit.lift_π (completedConstantComparisonCone X I φ hφ N) (op n)

end AlgebraicGeometry.Scheme
