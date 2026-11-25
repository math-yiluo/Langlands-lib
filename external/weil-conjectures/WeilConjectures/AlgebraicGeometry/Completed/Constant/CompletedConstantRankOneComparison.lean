/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantProjectionMaps
import all WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
import Mathlib.RingTheory.AdicCompletion.Completeness

/-! # The rank-one completed constant comparison

Source: Stacks Project, Modules on Sites, Tags 03EK and 093M, and completion Tag 05GG.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme

namespace CompletedConstantRankOne

open CompletedConstantProjection

private abbrev moduleForget (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] :=
  SheafOfModules.forget.{u + 1} (adicLisseRing X B) ⋙
    PresheafOfModules.toPresheaf (adicLisseRing X B).obj

private abbrev ringForget (X : Scheme.{u}) :=
  sheafToPresheaf (ProEt.topology X) CommRingCat.{u + 1} ⋙
    (Functor.whiskeringRight X.ProEtᵒᵖ CommRingCat.{u + 1} AddCommGrpCat.{u + 1}).obj
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})

-- Compare the additive and ring sheafifications of the constant rank-one module.
private noncomputable def constantUnitRaw (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] :
    (raw X B).obj (ModuleCat.of B B) ⟶
      (PresheafOfModules.restrictScalars (adicLisseConstantUnit X B)).obj
        (SheafOfModules.unit (adicLisseRing X B)).val := by
  let H := SheafOfModules.unit (adicLisseRing X B)
  refine
    { app := fun U ↦ ModuleCat.ofHom
        (Y := ((PresheafOfModules.restrictScalars
          (adicLisseConstantUnit X B)).obj H.val).obj U)
        { toFun := (adicLisseConstantUnit X B).app U
          map_add' := map_add ((adicLisseConstantUnit X B).app U).hom
          map_smul' := map_mul ((adicLisseConstantUnit X B).app U).hom }
      naturality := ?_ }
  intro U V f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  exact ConcreteCategory.congr_hom ((adicLisseConstantUnit X B).naturality f) b

private noncomputable def constantUnit (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] :
    (adicLisseConstantModules X B).obj (ModuleCat.of B B) ⟶
      SheafOfModules.unit (adicLisseRing X B) :=
  (PresheafOfModules.sheafificationHomEquiv.{u + 1}
    (adicLisseConstantUnit X B)).symm (constantUnitRaw X B)

private theorem constantUnit_generator (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (U : X.ProEtᵒᵖ) (b : B) :
    (constantUnit X B).val.app U
      (completedConstantGenerator X B (ModuleCat.of B B) U b) =
        (adicLisseConstantUnit X B).app U b := by
  have h := congrArg (PresheafOfModules.toPresheaf
    ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of B))).map
      ((PresheafOfModules.sheafificationHomEquiv.{u + 1}
        (adicLisseConstantUnit X B) (P := (raw X B).obj (ModuleCat.of B B))
          (F := SheafOfModules.unit (adicLisseRing X B))).apply_symm_apply
            (constantUnitRaw X B))
  rw [PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def] at h
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h U) b

private theorem constantUnit_isIso (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] :
    IsIso (constantUnit X B) := by
  let η := toSheafify (ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of B))
  let g := (moduleForget X B).map (constantUnit X B)
  let ζ := Functor.whiskerRight (adicLisseConstantUnit X B)
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})
  have h : η ≫ g = ζ := by
    ext U b
    exact constantUnit_generator X B U b
  have : Presheaf.IsLocallyInjective (ProEt.topology X) ζ :=
    (Presheaf.isLocallyInjective_forget_iff _ ζ).mp
      (inferInstanceAs (Presheaf.IsLocallyInjective (ProEt.topology X)
        (Functor.whiskerRight (adicLisseConstantUnit X B) (CategoryTheory.forget RingCat.{u + 1}))))
  have : Presheaf.IsLocallySurjective (ProEt.topology X) ζ :=
    (Presheaf.isLocallySurjective_iff_whisker_forget _ ζ).mpr
      (inferInstanceAs (Presheaf.IsLocallySurjective (ProEt.topology X)
        (Functor.whiskerRight (adicLisseConstantUnit X B) (CategoryTheory.forget RingCat.{u + 1}))))
  have : Presheaf.IsLocallyInjective (ProEt.topology X) (η ≫ g) := by
    rw [h]
    infer_instance
  have : Presheaf.IsLocallySurjective (ProEt.topology X) (η ≫ g) := by
    rw [h]
    infer_instance
  have : Presheaf.IsLocallyInjective (ProEt.topology X) g :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective _ η g
  have : Presheaf.IsLocallySurjective (ProEt.topology X) g :=
    Presheaf.isLocallySurjective_of_isLocallySurjective _ η g
  have : IsIso ((SheafOfModules.toSheaf _).map (constantUnit X B)) :=
    (Sheaf.isLocallyBijective_iff_isIso _).mp ⟨‹_›, ‹_›⟩
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf _)

-- Completion evaluation descends to a bijection on each finite quotient.
private noncomputable def quotientEval {A : Type (u + 1)} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    (AdicCompletion I A ⧸ (I ^ (n + 1) • ⊤ : Submodule A (AdicCompletion I A))) →ₗ[A]
      A ⧸ I ^ (n + 1) :=
  (I ^ (n + 1) • ⊤ : Submodule A (AdicCompletion I A)).liftQ
    (AdicCompletion.evalₐ I (n + 1)).toLinearMap (by
      intro c hc
      rw [AdicCompletion.pow_smul_top_eq_ker_eval (IsNoetherian.noetherian I)] at hc
      change AdicCompletion.eval I A (n + 1) c = 0 at hc
      change AdicCompletion.evalₐ I (n + 1) c = 0
      change (Ideal.quotientEquivAlgOfEq A (by simp)) (AdicCompletion.eval I A (n + 1) c) = 0
      rw [hc, map_zero])

private theorem quotientEval_bijective {A : Type (u + 1)} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (n : ℕ) : Function.Bijective (quotientEval I n) := by
  constructor
  · apply (injective_iff_map_eq_zero _).2
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | _ c =>
      apply (Submodule.Quotient.mk_eq_zero _).2
      rw [AdicCompletion.pow_smul_top_eq_ker_eval (IsNoetherian.noetherian I)]
      change AdicCompletion.eval I A (n + 1) c = 0
      change AdicCompletion.evalₐ I (n + 1) c = 0 at hx
      exact (map_eq_zero_iff _ (Ideal.quotientEquivAlgOfEq A (by simp)).injective).1 hx
  · intro a
    obtain ⟨c, hc⟩ := AdicCompletion.surjective_evalₐ I (n + 1) a
    exact ⟨Submodule.Quotient.mk c, hc⟩

private noncomputable def quotientEvalResidue {A : Type (u + 1)} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    (AdicCompletion I A ⧸ (I ^ (n + 1) • ⊤ : Submodule A (AdicCompletion I A))) →ₗ[
      A ⧸ I ^ (n + 1)] A ⧸ I ^ (n + 1) where
  toFun := quotientEval I n
  map_add' := map_add _
  map_smul' r x := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    change quotientEval I n (a • x) = _
    exact (quotientEval I n).map_smul a x

-- Retain quotient-ring linearity when identifying the finite additive sheaves.
private noncomputable def residueToRing (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    (moduleForget X A).obj ((adicLisseModuleSystem X I
      (completedConstantUnderlyingModule I (ModuleCat.of (AdicCompletion I A)
        (AdicCompletion I A)))).obj (op n)) ⟶
      (ringForget X).obj ((adicLisseRingSystem X I).obj (op n)) :=
  (moduleForget X (A ⧸ I ^ (n + 1))).map
    ((adicLisseConstantModules X (A ⧸ I ^ (n + 1))).map
      (ModuleCat.ofHom (quotientEvalResidue I n)) ≫ constantUnit X (A ⧸ I ^ (n + 1)))

private theorem residueToRing_isIso (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    IsIso (residueToRing X I n) := by
  have : IsIso (ModuleCat.ofHom (quotientEvalResidue I n)) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (quotientEval_bijective I n)
  have := constantUnit_isIso X (A ⧸ I ^ (n + 1))
  unfold residueToRing
  infer_instance

private theorem residueToRing_generator (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (n : ℕ)
    (U : X.ProEtᵒᵖ) (c : AdicCompletion I A) :
    (residueToRing X I n).app U
      (completedConstantGenerator X A (ModuleCat.of A
        (AdicCompletion I A ⧸ (I ^ (n + 1) • ⊤ : Submodule A (AdicCompletion I A)))) U
          (Submodule.Quotient.mk c)) =
      (adicLisseConstantUnit X (A ⧸ I ^ (n + 1))).app U
        (AdicCompletion.evalₐ I (n + 1) c) := by
  change (constantUnit X (A ⧸ I ^ (n + 1))).val.app U
    (((adicLisseConstantModules X (A ⧸ I ^ (n + 1))).map
      (ModuleCat.ofHom (quotientEvalResidue I n))).val.app U
        (completedConstantGenerator X (A ⧸ I ^ (n + 1)) _ U
          (Submodule.Quotient.mk c))) = _
  rw [constant_map_generator, constantUnit_generator]
  rfl

private theorem residueToRing_mul (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (n : ℕ)
    (U : X.ProEtᵒᵖ) (r : (adicLisseConstantRing X (A ⧸ I ^ (n + 1))).obj.obj U)
    (y : ((adicLisseModuleSystem X I (completedConstantUnderlyingModule I
      (ModuleCat.of (AdicCompletion I A) (AdicCompletion I A)))).obj (op n)).val.obj U) :
    (residueToRing X I n).app U
      (completedConstantResidueMul X I
        (ModuleCat.of (AdicCompletion I A) (AdicCompletion I A)) n U r y) =
      r * (show (adicLisseConstantRing X (A ⧸ I ^ (n + 1))).obj.obj U from
        (residueToRing X I n).app U y) :=
  (((adicLisseConstantModules X (A ⧸ I ^ (n + 1))).map
    (ModuleCat.ofHom (quotientEvalResidue I n)) ≫
      constantUnit X (A ⧸ I ^ (n + 1))).val.app U).hom.map_smul r y

-- The existing scalar-extension unit isomorphism has the expected tensor inverse.
private theorem unitIso_inv (X : Scheme.{u}) {B : Type (u + 1)} [CommRing B]
    {S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : adicLisseConstantRing X B ⟶ S) (U : X.ProEtᵒᵖ) (s : S.obj.obj U) :
    (CompletedConstantReduction.constantChange_unit X φ).inv.val.app U s =
      completedAdicChangeTensor X φ
        ((adicLisseConstantModules X B).obj (ModuleCat.of B B)) U s
        (completedConstantGenerator X B (ModuleCat.of B B) U 1) := by
  let κ := (PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((adicLisseForget X).obj S).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ
        ((adicLisseConstantModules X B).obj (ModuleCat.of B B)))
  change (eqToHom ((completedAdicChangeData X φ).choose_spec.choose _).symm).val.app U
    (s • κ.app U _) = (eqToHom
      ((completedAdicChangeData X φ).choose_spec.choose _).symm).val.app U (κ.app U _)
  congr 1
  rw [← (κ.app U).hom.map_smul]
  congr 1
  exact congrArg (fun b ↦ b ⊗ₜ[(adicLisseConstantRing X B).obj.obj U,
    (φ.hom.app U).hom] (completedConstantGenerator X B (ModuleCat.of B B) U 1)) (mul_one s)

private theorem ringMap_unit (X : Scheme.{u})
    {B D : Type (u + 1)} [CommRing B] [CommRing D] (f : B →+* D)
    (U : X.ProEtᵒᵖ) (b : B) :
    (((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom f)).hom.app U) ((adicLisseConstantUnit X B).app U b) =
        (adicLisseConstantUnit X D).app U (f b) :=
  (ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_naturality (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).map (CommRingCat.ofHom f))) U) b).symm

private theorem residueToRing_step (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I)
    (hφ : ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem X I) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom)) (n : ℕ) :
    (moduleForget X A).map ((adicLisseModuleSystem X I
      (completedConstantUnderlyingModule I
        (ModuleCat.of (AdicCompletion I A) (AdicCompletion I A)))).map
          (homOfLE (Nat.le_succ n)).op) ≫ residueToRing X I n =
      residueToRing X I (n + 1) ≫ (ringForget X).map
        ((adicLisseRingSystem X I).map (homOfLE (Nat.le_succ n)).op) := by
  apply sheafify_hom_ext (ProEt.topology X) _ _
    (SheafOfModules.unit (adicLisseRing X (A ⧸ I ^ (n + 1)))).isSheaf
  ext U x
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    change (residueToRing X I n).app U
      (((adicLisseModuleSystem X I (completedConstantUnderlyingModule I
        (ModuleCat.of (AdicCompletion I A) (AdicCompletion I A)))).map
          (homOfLE (Nat.le_succ n)).op).val.app U
            (completedConstantGenerator X A _ U (Submodule.Quotient.mk c))) =
      ((adicLisseRingSystem X I).map (homOfLE (Nat.le_succ n)).op).hom.app U
        ((residueToRing X I (n + 1)).app U
          (completedConstantGenerator X A _ U (Submodule.Quotient.mk c)))
    simp only [adicLisseModuleSystem, Functor.ofOpSequence_map_homOfLE_succ]
    erw [constant_map_generator]
    change (residueToRing X I n).app U
      (completedConstantGenerator X A _ U (Submodule.Quotient.mk c)) = _
    erw [residueToRing_generator, residueToRing_generator]
    have hn (k : ℕ) :
        (limit.π (adicLisseRingSystem X I) (op k)).hom.app U
          (φ.hom.app U ((adicLisseConstantUnit X (AdicCompletion I A)).app U c)) =
        (adicLisseConstantUnit X (A ⧸ I ^ (k + 1))).app U
          (AdicCompletion.evalₐ I (k + 1) c) := by
      exact (congrArg (fun f ↦ f.hom.app U
        ((adicLisseConstantUnit X (AdicCompletion I A)).app U c)) (hφ k)).trans
          (ringMap_unit X (AdicCompletion.evalₐ I (k + 1)).toRingHom U c)
    rw [← hn n, ← hn (n + 1)]
    exact (congrArg (fun f ↦ f.hom.app U
      (φ.hom.app U ((adicLisseConstantUnit X (AdicCompletion I A)).app U c)))
        (limit.w (adicLisseRingSystem X I) (homOfLE (Nat.le_succ n)).op)).symm

private noncomputable def systemsMap (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I)
    (hφ : ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem X I) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom)) :
    adicLisseModuleSystem X I (completedConstantUnderlyingModule I
      (ModuleCat.of (AdicCompletion I A) (AdicCompletion I A))) ⋙ moduleForget X A ⟶
        adicLisseRingSystem X I ⋙ ringForget X :=
  NatTrans.ofOpSequence (residueToRing X I) (residueToRing_step X I φ hφ)

private theorem systemsMap_isIso (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I)
    (hφ : ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem X I) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom)) :
    IsIso (systemsMap X I φ hφ) := by
  have (n : ℕᵒᵖ) : IsIso ((systemsMap X I φ hφ).app n) := residueToRing_isIso X I n.unop
  exact NatIso.isIso_of_isIso_app _

end CompletedConstantRankOne

open CompletedConstantRankOne

/-- The comparison is invertible for the rank-one free completion module.
Source: Stacks Project, Modules on Sites, Tags 03EK and 093M; More on Algebra,
Tag 05GG (completion modulo an ideal power).
(blueprint: lem-weil-pbc-completed-constant-rank-one-comparison).

Proof: write C = AdicCompletion I A and H = lim constant(A/I^(n+1)). The constant
C-module C is the unit module of constant C. Scalar extension takes it to the unit
module of H, via multiplication h tensor c -> h times phi(c). On the other side,
evaluation C -> A/I^(n+1) is surjective with kernel I^(n+1)C. The induced additive
quotient isomorphisms C/I^(n+1)C -> A/I^(n+1) commute with every transition and
with A-actions. Constant sheafification and the limit give an isomorphism from
the completed constant C-module to H with its restricted A-action. After these
two identifications the comparison is the identity on H: at every finite
projection its pure-tensor formula is projected(h) times eval(c), exactly the
formula of multiplication. Local tensor generation and the limit universal
property give equality with the fixed comparison map. All these identifications
remain valid for the zero ring, I=0 and I=top. -/
theorem completedConstantComparisonMap_rankOne_isIso (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I)
    (hφ : ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem X I) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom)) :
    IsIso (completedConstantComparisonMap X I φ hφ
      (ModuleCat.of (AdicCompletion I A) (AdicCompletion I A))) := by
  -- Transport the whole comparison cone to the coefficient ring limit cone.
  let N := ModuleCat.of (AdicCompletion I A) (AdicCompletion I A)
  let F := moduleForget X A
  let G := ringForget X
  let D := adicLisseModuleSystem X I (completedConstantUnderlyingModule I N)
  let c := F.mapCone (completedConstantComparisonCone X I φ hφ N)
  have := systemsMap_isIso X I φ hφ
  let e := asIso (systemsMap X I φ hφ)
  let s := F.mapIso ((SheafOfModules.restrictScalars ((adicLisseForget X).map
    (completedConstantBaseMap X I φ))).mapIso
      (CompletedConstantReduction.constantChange_unit X φ))
  let d := (Cone.postcompose e.hom).obj c
  have hd : d ≅ G.mapCone (limit.cone (adicLisseRingSystem X I)) := by
    refine Cone.ext s ?_
    intro n
    apply (cancel_epi s.inv).mp
    simp only [Iso.inv_hom_id_assoc]
    ext U r
    change (adicLisseCompletedRing X I).obj.obj U at r
    change (residueToRing X I n.unop).app U
      ((completedConstantProjection X I φ hφ N n.unop).val.app U
        ((CompletedConstantReduction.constantChange_unit X φ).inv.val.app U r)) =
      (limit.π (adicLisseRingSystem X I) n).hom.app U r
    rw [unitIso_inv, (completedConstantProjection_spec X I φ hφ N n.unop).1]
    rw [residueToRing_mul]
    erw [residueToRing_generator]
    simp only [map_one, mul_one]
  have hc : IsLimit c := (IsLimit.postcomposeHomEquiv e c)
    (IsLimit.ofIsoLimit (isLimitOfPreserves G (limit.isLimit _)) hd.symm)
  have : ReflectsLimit D F := reflectsLimit_of_reflectsIsomorphisms D F
  exact (IsLimit.nonempty_isLimit_iff_isIso_lift (limit.isLimit D)).mp
    ⟨isLimitOfReflects F hc⟩

end AlgebraicGeometry.Scheme
