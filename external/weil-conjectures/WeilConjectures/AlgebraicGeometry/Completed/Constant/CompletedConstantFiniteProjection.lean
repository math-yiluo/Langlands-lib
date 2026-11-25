/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompletedConstantProjection.CompletedConstantResidueData
import all WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
/-! # Canonical finite projections of completed constant realization

Source: Stacks Project, Modules on Sites, Tags 03EK and 093J--093M.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme
namespace CompletedConstantProjection

attribute [local irreducible] constantMap

private theorem base_projection (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I)
    (hφ : ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem X I) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom)) (n : ℕ) :
    completedConstantBaseMap X I φ ≫ limit.π (adicLisseRingSystem X I) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) := by
  unfold completedConstantBaseMap
  rw [Category.assoc, hφ, ← Functor.map_comp]
  congr 1

private def residueIdentity {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (N : ModuleCat.{u + 1} (AdicCompletion I A)) (n : ℕ) :
    ModuleCat.of A (completedConstantUnderlyingModule I N ⧸
      (I ^ (n + 1) • ⊤ : Submodule A (completedConstantUnderlyingModule I N)))
        →ₛₗ[Ideal.Quotient.mk (I ^ (n + 1))]
      ModuleCat.of (A ⧸ I ^ (n + 1)) (completedConstantUnderlyingModule I N ⧸
        (I ^ (n + 1) • ⊤ : Submodule A (completedConstantUnderlyingModule I N))) where
  toFun := id
  map_add' := fun _ _ ↦ rfl
  map_smul' a x := by
    induction x using Submodule.Quotient.induction_on with
    | _ x => exact (Module.Quotient.mk_smul_mk
        (completedConstantUnderlyingModule I N) (I ^ (n + 1)) a x).symm

private theorem residueMul_constScalar (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (N : ModuleCat.{u + 1} (AdicCompletion I A)) (n : ℕ) (U : X.ProEtᵒᵖ)
    (a : (adicLisseConstantRing X A).obj.obj U)
    (y : ((adicLisseModuleSystem X I (completedConstantUnderlyingModule I N)).obj
      (op n)).val.obj U) :
    completedConstantResidueMul X I N n U
      (((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))).hom.app U a) y = a • y := by
  exact constantScalar_compatibility X (Ideal.Quotient.mk (I ^ (n + 1)))
    (completedConstantUnderlyingModule I N ⧸
      (I ^ (n + 1) • ⊤ : Submodule A (completedConstantUnderlyingModule I N)))
    (residueIdentity I N n) rfl U a y

private def residueComparison (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I)
    (hφ : ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem X I) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom))
    (N : ModuleCat.{u + 1} (AdicCompletion I A)) (n : ℕ) :
    ((adicLisseModuleSystem X I (completedConstantUnderlyingModule I N)).obj (op n)) ≅
      (SheafOfModules.restrictScalars ((adicLisseForget X).map
        (completedConstantBaseMap X I φ))).obj
        ((SheafOfModules.restrictScalars ((adicLisseForget X).map
          (limit.π (adicLisseRingSystem X I) (op n)))).obj
            (completedConstantResidueModule X I N n)) := by
  let q := residueIdentity I N n
  let g := constantMap X (Ideal.Quotient.mk (I ^ (n + 1)))
    (completedConstantBaseMap X I φ) (limit.π (adicLisseRingSystem X I) (op n))
    (base_projection X I φ hφ n) _ _ q
  have := constantMap_isIso X (Ideal.Quotient.mk (I ^ (n + 1)))
    (completedConstantBaseMap X I φ) (limit.π (adicLisseRingSystem X I) (op n))
    (base_projection X I φ hφ n) _ _ q Function.bijective_id
  exact asIso g

private theorem residueComparison_hom (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I)
    (hφ : ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem X I) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom))
    (N : ModuleCat.{u + 1} (AdicCompletion I A)) (n : ℕ) (U : X.ProEtᵒᵖ)
    (y : ((adicLisseModuleSystem X I (completedConstantUnderlyingModule I N)).obj
      (op n)).val.obj U) :
    (residueComparison X I φ hφ N n).hom.val.app U y = y := by
  have h := constantMap_underlying X (Ideal.Quotient.mk (I ^ (n + 1)))
    (completedConstantBaseMap X I φ) (limit.π (adicLisseRingSystem X I) (op n))
    (base_projection X I φ hφ n) _ _ (residueIdentity I N n)
  have hid : AddCommGrpCat.ofHom (residueIdentity I N n).toAddMonoidHom = 𝟙 _ := rfl
  rw [hid, CategoryTheory.Functor.map_id] at h
  exact congrArg (fun k ↦ k.hom.app U y) h

private theorem residueComparison_inv (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I)
    (hφ : ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem X I) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom))
    (N : ModuleCat.{u + 1} (AdicCompletion I A)) (n : ℕ) (U : X.ProEtᵒᵖ)
    (y : (completedConstantResidueModule X I N n).val.obj U) :
    (residueComparison X I φ hφ N n).inv.val.app U y = y := by
  have h := congrArg (fun k ↦ k.val.app U y)
    (residueComparison X I φ hφ N n).inv_hom_id
  change (residueComparison X I φ hφ N n).hom.val.app U
    ((residueComparison X I φ hφ N n).inv.val.app U y) = y at h
  rwa [residueComparison_hom] at h

attribute [local irreducible] residueComparison

private def extensionResidue (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I)
    (hφ : ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem X I) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom))
    (N : ModuleCat.{u + 1} (AdicCompletion I A)) (n : ℕ) :
    (completedConstantRealization X I φ).obj N ⟶
      (SheafOfModules.restrictScalars ((adicLisseForget X).map
        (limit.π (adicLisseRingSystem X I) (op n)))).obj
          (completedConstantResidueModule X I N n) := by
  let M := (adicLisseConstantModules X (AdicCompletion I A)).obj N
  let T := (SheafOfModules.restrictScalars ((adicLisseForget X).map
    (limit.π (adicLisseRingSystem X I) (op n)))).obj
      (completedConstantResidueModule X I N n)
  let g := constantMap X (AdicCompletion.evalₐ I (n + 1)).toRingHom φ
    (limit.π (adicLisseRingSystem X I) (op n)) (hφ n) N
      (ModuleCat.of (A ⧸ I ^ (n + 1)) (completedConstantUnderlyingModule I N ⧸
        (I ^ (n + 1) • ⊤ : Submodule A (completedConstantUnderlyingModule I N))))
      (residueMap I N n)
  let e := (completedAdicChangeData X φ).choose_spec.choose M
  exact eqToHom e ≫ (CompletedConstantReduction.tensorHomEquiv X φ M T).symm g

private def projection (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I)
    (hφ : ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem X I) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom))
    (N : ModuleCat.{u + 1} (AdicCompletion I A)) (n : ℕ) :
    (SheafOfModules.restrictScalars ((adicLisseForget X).map
      (completedConstantBaseMap X I φ))).obj
        ((completedConstantRealization X I φ).obj N) ⟶
      (adicLisseModuleSystem X I (completedConstantUnderlyingModule I N)).obj (op n) :=
  (SheafOfModules.restrictScalars ((adicLisseForget X).map
    (completedConstantBaseMap X I φ))).map (extensionResidue X I φ hφ N n) ≫
      (residueComparison X I φ hφ N n).inv

private theorem projection_apply (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I)
    (hφ : ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem X I) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom))
    (N : ModuleCat.{u + 1} (AdicCompletion I A)) (n : ℕ) (U : X.ProEtᵒᵖ)
    (x : ((completedConstantRealization X I φ).obj N).val.obj U) :
    (projection X I φ hφ N n).val.app U x =
      (extensionResidue X I φ hφ N n).val.app U x := by
  exact residueComparison_inv X I φ hφ N n U _

attribute [local irreducible] projection

private theorem projection_pure (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I)
    (hφ : ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem X I) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom))
    (N : ModuleCat.{u + 1} (AdicCompletion I A)) (n : ℕ) (U : X.ProEtᵒᵖ)
    (r : (adicLisseCompletedRing X I).obj.obj U) (x : N) :
    (projection X I φ hφ N n).val.app U
      (completedAdicChangeTensor X φ ((adicLisseConstantModules X _).obj N) U r
        (completedConstantGenerator X _ N U x)) =
      completedConstantResidueMul X I N n U
        ((limit.π (adicLisseRingSystem X I) (op n)).hom.app U r)
        (completedConstantGenerator X A
          (ModuleCat.of A (completedConstantUnderlyingModule I N ⧸
            (I ^ (n + 1) • ⊤ : Submodule A (completedConstantUnderlyingModule I N)))) U
          ((I ^ (n + 1) • ⊤ : Submodule A
            (completedConstantUnderlyingModule I N)).mkQ x)) := by
  rw [projection_apply]
  let M := (adicLisseConstantModules X (AdicCompletion I A)).obj N
  let T := (SheafOfModules.restrictScalars ((adicLisseForget X).map
    (limit.π (adicLisseRingSystem X I) (op n)))).obj
      (completedConstantResidueModule X I N n)
  let g := constantMap X (AdicCompletion.evalₐ I (n + 1)).toRingHom φ
    (limit.π (adicLisseRingSystem X I) (op n)) (hφ n) N
      (ModuleCat.of (A ⧸ I ^ (n + 1)) (completedConstantUnderlyingModule I N ⧸
        (I ^ (n + 1) • ⊤ : Submodule A (completedConstantUnderlyingModule I N))))
      (residueMap I N n)
  let r₀ := (CompletedConstantReduction.tensorHomEquiv X φ M T).symm g
  let e := (completedAdicChangeData X φ).choose_spec.choose M
  change (eqToHom e.symm ≫ (eqToHom e ≫ r₀)).val.app U
    ((toSheafify (ProEt.topology X)
      (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app U
        (r ⊗ₜ[(adicLisseConstantRing X (AdicCompletion I A)).obj.obj U,
          (φ.hom.app U).hom] completedConstantGenerator X _ N U x)) = _
  rw [← Category.assoc, eqToHom_trans]
  simp only [eqToHom_refl, Category.id_comp]
  rw [CompletedConstantReduction.tensorHomEquiv_tmul]
  rw [show CompletedConstantReduction.tensorHomEquiv X φ M T r₀ = g from
    (CompletedConstantReduction.tensorHomEquiv X φ M T).apply_symm_apply g]
  rw [constantMap_generator]
  rfl

attribute [local irreducible] extensionResidue

private theorem projection_linear (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I)
    (hφ : ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem X I) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom))
    (N : ModuleCat.{u + 1} (AdicCompletion I A)) (n : ℕ) (U : X.ProEtᵒᵖ)
    (r : (adicLisseCompletedRing X I).obj.obj U)
    (a : (adicLisseConstantRing X A).obj.obj U)
    (x : ((completedConstantRealization X I φ).obj N).val.obj U)
    (ha : ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))).hom.app U a =
        (limit.π (adicLisseRingSystem X I) (op n)).hom.app U r) :
    (projection X I φ hφ N n).val.app U (r • x) =
      a • (projection X I φ hφ N n).val.app U x := by
  let y := (projection X I φ hφ N n).val.app U x
  have hr : (projection X I φ hφ N n).val.app U (r • x) =
      completedConstantResidueMul X I N n U
        ((limit.π (adicLisseRingSystem X I) (op n)).hom.app U r) y := by
    refine (projection_apply X I φ hφ N n U (r • x)).trans ?_
    refine (((extensionResidue X I φ hφ N n).val.app U).hom.map_smul r x).trans ?_
    exact congrArg (fun z : (completedConstantResidueModule X I N n).val.obj U ↦
      (limit.π (adicLisseRingSystem X I) (op n)).hom.app U r • z)
        (projection_apply X I φ hφ N n U x).symm
  exact hr.trans ((congrArg (fun s ↦ completedConstantResidueMul X I N n U s y)
    ha.symm).trans (residueMul_constScalar X I N n U a y))

end CompletedConstantProjection
/-- The fixed generator formula and completed-scalar linearity of a finite projection.
Source: Stacks Tags 03EK and 093J--093M
(blueprint: def-weil-pbc-completed-constant-finite-projections). -/
def CompletedConstantProjectionSpec (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I)
    (N : ModuleCat.{u + 1} (AdicCompletion I A)) (n : ℕ)
    (q : (SheafOfModules.restrictScalars ((adicLisseForget X).map
      (completedConstantBaseMap X I φ))).obj
        ((completedConstantRealization X I φ).obj N) ⟶
          (adicLisseModuleSystem X I (completedConstantUnderlyingModule I N)).obj (op n)) :
    Prop :=
  (∀ (U : X.ProEtᵒᵖ) (r : (adicLisseCompletedRing X I).obj.obj U) (x : N),
    q.val.app U (completedAdicChangeTensor X φ ((adicLisseConstantModules X _).obj N) U r
      (completedConstantGenerator X _ N U x)) =
        completedConstantResidueMul X I N n U
          ((limit.π (adicLisseRingSystem X I) (op n)).hom.app U r)
          (completedConstantGenerator X A
            (ModuleCat.of A (completedConstantUnderlyingModule I N ⧸
              (I ^ (n + 1) • ⊤ : Submodule A (completedConstantUnderlyingModule I N)))) U
            ((I ^ (n + 1) • ⊤ : Submodule A
              (completedConstantUnderlyingModule I N)).mkQ x))) ∧
  (∀ (U : X.ProEtᵒᵖ)
      (r : (adicLisseCompletedRing X I).obj.obj U)
      (a : (adicLisseConstantRing X A).obj.obj U)
      (x : ((completedConstantRealization X I φ).obj N).val.obj U),
    ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))).hom.app U a =
        (limit.π (adicLisseRingSystem X I) (op n)).hom.app U r →
    q.val.app U (r • x) = a • q.val.app U x)

/-- A finite residue map exists with its actual tensor formula. No finiteness of N is
needed for this construction. Source: Stacks Tag 03EK, followed by Tags 093J--093M.

Proof: give N/I^k N its quotient-ring action. Completion evaluation is compatible with
this action: a completed scalar and an A-scalar with the same residue differ by I^k C,
whose products with N belong to I^k N. Sheafify this semilinear residue map and apply the
extension-of-scalars universal property. The quotient module has the same underlying
constant abelian sheaf whether its ring is A or A/I^k. The identity on that abelian
sheaf is A-linear, by the naturality of the constant-ring unit, and gives the displayed
target. The tensor universal property gives the pure formula. Linearity over H followed
by restriction to A gives the second formula whenever the two residues coincide.
(blueprint: def-weil-pbc-completed-constant-finite-projections). -/
theorem completedConstantProjection_exists (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I)
    (hφ : ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem X I) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom))
    (N : ModuleCat.{u + 1} (AdicCompletion I A)) (n : ℕ) :
    ∃ q : (SheafOfModules.restrictScalars ((adicLisseForget X).map
      (completedConstantBaseMap X I φ))).obj
        ((completedConstantRealization X I φ).obj N) ⟶
          (adicLisseModuleSystem X I (completedConstantUnderlyingModule I N)).obj (op n),
      CompletedConstantProjectionSpec X I φ N n q := by
  refine ⟨CompletedConstantProjection.projection X I φ hφ N n, ?_⟩
  exact ⟨CompletedConstantProjection.projection_pure X I φ hφ N n,
    CompletedConstantProjection.projection_linear X I φ hφ N n⟩

/-- The finite projection specified by its tensor formula, constructed by the preceding
proved existence theorem. Source: Stacks Tags 03EK and 093J--093M
(blueprint: def-weil-pbc-completed-constant-finite-projections). -/
def completedConstantProjection (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I)
    (hφ : ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem X I) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom))
    (N : ModuleCat.{u + 1} (AdicCompletion I A)) (n : ℕ) :=
  (completedConstantProjection_exists X I φ hφ N n).choose

/-- Both finite-projection identities. Source: Stacks Tags 03EK and 093J--093M
(blueprint: def-weil-pbc-completed-constant-finite-projections). -/
theorem completedConstantProjection_spec (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I)
    (hφ : ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem X I) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom))
    (N : ModuleCat.{u + 1} (AdicCompletion I A)) (n : ℕ) :
    CompletedConstantProjectionSpec X I φ N n (completedConstantProjection X I φ hφ N n) :=
  (completedConstantProjection_exists X I φ hφ N n).choose_spec

end AlgebraicGeometry.Scheme
