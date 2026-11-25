/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfIntegralReductionTower
public import WeilConjectures.AlgebraicGeometry.Koszul.KoszulReconstructionModels
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
import all WeilConjectures.RingTheory.KoszulProjectiveResolution

/-! # The degree-zero quotient cycle of the completed exterior Koszul complex

Source: Stacks Project, Tags 091N and 099M.
(blueprint: new-p6-completed-koszul-quotient-projection).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

attribute [local instance] WeilConjectures.sfAbSheafify

attribute [local instance] WeilConjectures.sfAbBijective

attribute [local instance] AlgebraicGeometry.ProEtale.VaryingRing.ringSheafify

variable (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)

private theorem moduleIso_inv_apply {R : Type*} [Ring R] {M N : ModuleCat R}
    (e : M ≅ N) (x : N) : e.hom (e.inv x) = x :=
  ConcreteCategory.congr_hom e.inv_hom_id x

/-- The degree-zero residue projection of the completed Koszul complex kills boundaries.
Source: Stacks Project, Tag 0623, Koszul augmentation; Tags 03DA and 03EK,
module sheafification and scalar extension.
(blueprint: new-p6-completed-koszul-quotient-projection).
Proof: identify exterior degree zero with the coefficient ring and compose with
A → A/I^(n+1). The degree-one Koszul boundary is the linear combination of the
powers a_i^(n+1), so its residue is zero. On constant presheaves map x to the
constant section of that residue. This map is linear for the composite scalar
map by the recorded residue normalization. Extend it first by module
sheafification, then by the normalized scalar-extension adjunction. Their
section formulas give the required unit normalization, and naturality of the
adjunction transports the zero boundary composite. -/
theorem completedKoszulQuotientProjection_exists
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) (n : ℕ) :
    ∃ p : (completedAdicKoszul T d r a n).X 0 ⟶ completedAdicFiniteModule T d n,
      completedAdicKoszulUnitZero T d r a n ≫ p = reconstructionQuotientUnit T d n ∧
      (completedAdicKoszul T d r a n).d (-1) 0 ≫ p = 0 := by
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0} T
  have := (koszulConstantUnit_local T A).1
  have := (koszulConstantUnit_local T A).2
  let α := completedAdicScalar T d
  let G := koszulConstantFunctor T A
  let C := koszulPower A r a n
  let K := ExteriorAlgebra.koszulComplex (ULift.{t + 1} A) r
    (fun i ↦ ULift.up (a i ^ (n + 1)))
  let z : C.X 0 ≅ ModuleCat.of (ULift.{t + 1} A) (ULift.{t + 1} A) :=
    K.extendXIso ComplexShape.embeddingDownNat (i := 0) rfl ≪≫
      (exteriorPower.zeroEquiv (ULift.{t + 1} A) (Fin r →₀ ULift.{t + 1} A)).toModuleIso
  let q : ULift.{t + 1} A →+* completedAdicQuotient d n :=
    RingHom.ulift (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
  have hboundary (x : C.X (-1)) : q (z.hom ((C.d (-1) 0) x)) = 0 := by
    have he : C.d (-1) 0 ≫ z.hom =
        (K.extendXIso ComplexShape.embeddingDownNat (i := 1) rfl).hom ≫
          ModuleCat.ofHom ((exteriorPower.zeroEquiv (ULift.{t + 1} A)
            (Fin r →₀ ULift.{t + 1} A)).toLinearMap.comp
              (ExteriorAlgebra.koszulBoundary (ULift.{t + 1} A) r
                (fun i ↦ ULift.up (a i ^ (n + 1))) 0)) := by
      have hd : C.d (-1) 0 =
          (K.extendXIso ComplexShape.embeddingDownNat (i := 1) rfl).hom ≫ K.d 1 0 ≫
            (K.extendXIso ComplexShape.embeddingDownNat (i := 0) rfl).inv :=
        HomologicalComplex.extend_d_eq K ComplexShape.embeddingDownNat
          (i := 1) (j := 0) (i' := -1) (j' := 0) rfl rfl
      rw [hd]
      dsimp only [z, Iso.trans_hom]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rfl
    change q ((C.d (-1) 0 ≫ z.hom) x) = 0
    rw [he]
    change q (exteriorPower.zeroEquiv (ULift.{t + 1} A) (Fin r →₀ ULift.{t + 1} A)
      (ExteriorAlgebra.koszulBoundary (ULift.{t + 1} A) r
        (fun i ↦ ULift.up (a i ^ (n + 1))) 0 _)) = 0
    rw [ExteriorAlgebra.koszulBoundary_zero_quotient_formula]
    suffices ∀ v : Fin r →₀ ULift.{t + 1} A,
        q (Finsupp.linearCombination (ULift.{t + 1} A)
          (fun i ↦ ULift.up (a i ^ (n + 1))) v) = 0 from this _
    intro v
    induction v using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add v w hv hw => simp only [map_add, hv, hw, add_zero]
    | single i c =>
      rw [Finsupp.linearCombination_single, smul_eq_mul, map_mul]
      have hmem : a i ^ (n + 1) ∈ d.ideal ^ (n + 1) :=
        Ideal.pow_mem_pow (ha ▸ Ideal.subset_span (Set.mem_range_self i)) _
      have hq : q (ULift.up (a i ^ (n + 1))) = 0 :=
        congrArg ULift.up (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
      rw [hq, mul_zero]
  let σ : (Functor.const T.ProEtᵒᵖ).obj (RingCat.of (completedAdicQuotient d n)) ⟶
      (completedAdicFiniteRing T d n).obj :=
    ProEtale.finiteCoefficientScalarMap T (completedAdicQuotient d n)
  let N := (SheafOfModules.restrictScalars.{t + 1}
    ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map α)).obj
      (completedAdicFiniteModule T d n)
  let P := (siteConstantModulePresheafGeneral (C := T.ProEt) (ULift.{t + 1} A)).obj (C.X 0)
  let D := (PresheafOfModules.restrictScalars (koszulConstantUnit T A)).obj N.val
  let g₀ : P ⟶ D :=
    { app := fun U ↦ ModuleCat.ofHom (X := P.obj U) (Y := D.obj U)
        { toFun := fun x ↦ (σ.app U) (q (z.hom x))
          map_add' := by intros; simp only [map_add]
          map_smul' := by
            intro c x
            change (σ.app U) (q (z.hom (c • x))) =
              (completedAdicProjection T d n).hom.app U
                (α.hom.app U ((koszulConstantUnit T A).app U c)) *
                  (σ.app U) (q (z.hom x))
            rw [map_smul, smul_eq_mul, map_mul, map_mul]
            exact congrArg
              (fun y : (completedAdicFiniteRing T d n).obj.obj U ↦
                y * (σ.app U) (q (z.hom x)))
              ((completedAdicScalar_exists T d).exists.choose_spec n U c).symm }
      naturality := fun {U V} f ↦ by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact NatTrans.naturality_apply σ f (q (z.hom x)) }
  let g : G.obj (C.X 0) ⟶ N :=
    (PresheafOfModules.sheafificationHomEquiv (koszulConstantUnit T A)).symm g₀
  let adj := (completedAdjunction T α).choose
  let p := (adj.homEquiv (G.obj (C.X 0)) (completedAdicFiniteModule T d n)).symm g
  have hg (U : T.ProEtᵒᵖ) (x : C.X 0) :
      g.val.app U ((toSheafify (ProEt.topology T) P.presheaf).app U x) =
        (σ.app U) (q (z.hom x)) := by
    have he := PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def
      (koszulConstantUnit T A) g
    have hh := congrArg (fun h ↦ (PresheafOfModules.toPresheaf _).map h)
      ((PresheafOfModules.sheafificationHomEquiv (koszulConstantUnit T A)
        (P := P) (F := N)).apply_symm_apply g₀)
    exact congrArg (fun h ↦ h.app U x) (he.symm.trans hh)
  have hp (U : T.ProEtᵒᵖ) (x : (G.obj (C.X 0)).val.obj U) :
      p.val.app U (completedAdicScalarTensor T d _ U 1 x) = g.val.app U x := by
    have h := (completedAdjunction T α).choose_spec _ _ p U x
    rw [(adj.homEquiv _ _).apply_symm_apply] at h
    exact h.symm
  have hG {M M' : ModuleCat.{t + 1} (ULift.{t + 1} A)} (f : M ⟶ M')
      (U : T.ProEtᵒᵖ) (x : M) :
      (G.map f).val.app U
          ((toSheafify (ProEt.topology T)
            (((siteConstantModulePresheafGeneral (C := T.ProEt)
              (ULift.{t + 1} A)).obj M).presheaf)).app U x) =
        (toSheafify (ProEt.topology T)
          (((siteConstantModulePresheafGeneral (C := T.ProEt)
            (ULift.{t + 1} A)).obj M').presheaf)).app U (f x) := by
    exact (congrArg (fun h ↦ h.app U x)
      (toSheafify_naturality (ProEt.topology T)
        ((PresheafOfModules.toPresheaf _).map
          ((siteConstantModulePresheafGeneral (C := T.ProEt)
            (ULift.{t + 1} A)).map f)))).symm
  refine ⟨p, ?_, ?_⟩
  · apply (completedAdicFiniteModule T d n).unitHomEquiv.injective
    apply PresheafOfModules.sections_ext
    intro U
    change p.val.app U ((completedAdicKoszulUnitZero T d r a n).val.app U
      (1 : (completedAdicRing T d).obj.obj U)) =
        (reconstructionQuotientUnit T d n).val.app U (1 : (completedAdicRing T d).obj.obj U)
    apply (congrArg (fun x ↦ p.val.app U x)
      ((completedAdicKoszulUnitZero_exists T d r a n).exists.choose_spec U)).trans
    apply (hp U _).trans
    apply Eq.trans ?_
      ((reconstructionQuotientUnit_exists T d n).exists.choose_spec U).symm
    have hk : koszulSheafUnitZero T A r a n = koszulConstantOne T A ≫ G.map z.inv := by
      dsimp only [z, Iso.trans_inv]
      rw [Functor.map_comp]
      rfl
    apply (congrArg (fun h ↦ g.val.app U
      (h.val.app U (1 : (adicModuleRing T A).obj.obj U))) hk).trans
    apply (congrArg (fun x ↦ g.val.app U ((G.map z.inv).val.app U x))
      ((koszulConstantOne_exists T A).exists.choose_spec U)).trans
    apply (congrArg (fun x ↦ g.val.app U x) (hG z.inv U 1)).trans
    apply (hg U _).trans
    have hz : z.hom (z.inv (1 : ULift.{t + 1} A)) = 1 :=
      moduleIso_inv_apply z (1 : ULift.{t + 1} A)
    exact (congrArg (fun x ↦ (σ.app U) (q x)) hz).trans
      ((congrArg (fun x ↦ (σ.app U) x) (map_one q)).trans (map_one (σ.app U).hom))
  · have hgzero : G.map (C.d (-1) 0) ≫ g = 0 := by
      apply (PresheafOfModules.sheafificationHomEquiv (koszulConstantUnit T A)).injective
      apply PresheafOfModules.hom_ext
      intro U
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change g.val.app U ((G.map (C.d (-1) 0)).val.app U
        ((toSheafify (ProEt.topology T)
          (((siteConstantModulePresheafGeneral (C := T.ProEt)
            (ULift.{t + 1} A)).obj (C.X (-1))).presheaf)).app U x)) = 0
      rw [hG, hg, hboundary, map_zero]
    apply (adj.homEquiv _ _).injective
    change adj.homEquiv _ _ ((completedAdicScalarExtension T d).map
      (G.map (C.d (-1) 0)) ≫ p) = adj.homEquiv _ _ 0
    apply (adj.homEquiv_naturality_left (G.map (C.d (-1) 0)) p).trans
    apply (congrArg (fun h ↦ G.map (C.d (-1) 0) ≫ h)
      ((adj.homEquiv _ _).apply_symm_apply g)).trans
    apply hgzero.trans
    symm
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ((completedAdjunction T α).choose_spec _ _ 0 U x).symm

end AlgebraicGeometry.Scheme
