/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.AdicCompletion.Algebra
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-! # Completed affine sections of a power-torsion sheaf -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

open scoped TensorProduct in
private theorem tensor_ideal_range {A S T : Type u} [CommRing A]
    [AddCommGroup S] [Module A S] [AddCommGroup T] [Module A T] (K : Ideal A) :
    LinearMap.range (TensorProduct.map
      (K • (⊤ : Submodule A S)).subtype (LinearMap.id : T →ₗ[A] T)) =
      K • (⊤ : Submodule A (S ⊗[A] T)) := by
  rw [TensorProduct.range_map, Submodule.range_subtype, LinearMap.range_id]
  apply le_antisymm
  · apply Submodule.map₂_le.mpr
    intro s hs t ht
    simp only [TensorProduct.mk_apply]
    refine Submodule.smul_induction_on hs ?_ ?_
    · intro a ha x hx
      rw [← TensorProduct.smul_tmul']
      exact Submodule.smul_mem_smul ha (Submodule.mem_top)
    · intro x y hx hy
      rw [TensorProduct.add_tmul]
      exact Submodule.add_mem _ hx hy
  · apply Submodule.smul_le.mpr
    intro a ha z hz
    clear hz
    induction z using TensorProduct.inductionOn with
    | tmul s t =>
      rw [TensorProduct.smul_tmul']
      exact Submodule.apply_mem_map₂ _
        (Submodule.smul_mem_smul ha (Submodule.mem_top)) (Submodule.mem_top)
    | add x y hx hy =>
      rw [smul_add]
      exact Submodule.add_mem _ hx hy

open scoped TensorProduct in
/-- The quotient equivalence is the tensor unit, without a finite-module hypothesis.
Source: Stacks, Tag 05GG and right exactness of tensor, used in Tag 0889(1).
Proof: quotient the completion evaluation by its kernel, tensor that equivalence,
and use the tensor/quotient equivalence. Its value on 1 tensor x is the unit. -/
private theorem adic_tensor_unit_quotient {A : Type u} [CommRing A]
    (I : Ideal A) (hI : I.FG) (T : ModuleCat.{u} A) (n : ℕ) :
    ∃ e : (T ⧸ (I ^ n • (⊤ : Submodule A T))) ≃ₗ[A]
        ((AdicCompletion I A ⊗[A] T) ⧸
          (I ^ n • (⊤ : Submodule A (AdicCompletion I A ⊗[A] T)))),
      ∀ x : T, e (Submodule.Quotient.mk x) =
        Submodule.Quotient.mk ((1 : AdicCompletion I A) ⊗ₜ[A] x) := by
  let S := AdicCompletion I A
  let K := I ^ n
  let p : Submodule A S := K • ⊤
  let ev := AdicCompletion.eval I A n
  have hp : p = ev.ker := AdicCompletion.pow_smul_top_eq_ker_eval (M := A) hI
  have hK : (K • (⊤ : Submodule A A)) = K := by simp
  let eS : (S ⧸ p) ≃ₗ[A] (A ⧸ K) :=
    (Submodule.quotEquivOfEq _ _ hp) ≪≫ₗ
      ev.quotKerEquivOfSurjective (AdicCompletion.eval_surjective I A n) ≪≫ₗ
      (Submodule.quotEquivOfEq _ _ hK)
  let eQ := TensorProduct.quotientTensorEquiv T p ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (tensor_ideal_range (S := S) (T := T) K)
  let e := (TensorProduct.quotTensorEquivQuotSMul T K).symm ≪≫ₗ
    TensorProduct.congr eS.symm (LinearEquiv.refl A T) ≪≫ₗ eQ
  refine ⟨e, ?_⟩
  intro x
  have h1 : eS (Submodule.Quotient.mk (1 : S)) = (1 : A ⧸ K) := by
    simp only [eS, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk]
    change (Submodule.quotEquivOfEq _ _ hK) (ev (1 : S)) = _
    change (Submodule.quotEquivOfEq _ _ hK)
      (AdicCompletion.eval I A n (AdicCompletion.of I A 1)) = _
    rw [AdicCompletion.eval_of]
    rfl
  have h1' : eS.symm (1 : A ⧸ K) = Submodule.Quotient.mk (1 : S) :=
    eS.symm_apply_eq.mpr h1.symm
  change eQ ((TensorProduct.congr eS.symm (LinearEquiv.refl A T))
    ((TensorProduct.quotTensorEquivQuotSMul T K).symm (Submodule.Quotient.mk x))) = _
  rw [
    TensorProduct.quotTensorEquivQuotSMul_symm_mk, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, h1']
  rfl

open scoped TensorProduct in
private theorem adic_tensor_unit_bijective {A : Type u} [CommRing A]
    (I : Ideal A) (hI : I.FG) (T : ModuleCat.{u} A) (n : ℕ)
    (hzero : I ^ n • (⊤ : Submodule A T) = ⊥) :
    Function.Bijective (TensorProduct.mk A (AdicCompletion I A) T
      (1 : AdicCompletion I A)) := by
  let S := AdicCompletion I A
  let K := I ^ n
  have hz (a : A) (ha : a ∈ K) (x : T) : a • x = 0 := by
    have h : a • x ∈ I ^ n • (⊤ : Submodule A T) :=
      Submodule.smul_mem_smul ha (Submodule.mem_top)
    rw [hzero] at h
    simpa only [Submodule.mem_bot] using h
  have ht : K • (⊤ : Submodule A (S ⊗[A] T)) = ⊥ := by
    apply le_antisymm ?_ bot_le
    apply Submodule.smul_le.mpr
    intro a ha z hz
    clear hz
    change a • z = 0
    induction z using TensorProduct.inductionOn with
    | tmul s x => rw [← TensorProduct.tmul_smul, hz a ha x, TensorProduct.tmul_zero]
    | add x y hx hy => simp only [smul_add, hx, hy, add_zero]
  obtain ⟨e, he⟩ := adic_tensor_unit_quotient I hI T n
  have hinj : Function.Injective (K • (⊤ : Submodule A T)).mkQ := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.ker_mkQ]
    exact hzero
  have htinj : Function.Injective (K • (⊤ : Submodule A (S ⊗[A] T))).mkQ := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.ker_mkQ, ht]
  constructor
  · intro x y hxy
    apply hinj
    apply e.injective
    exact (he x).trans ((congrArg Submodule.Quotient.mk hxy).trans (he y).symm)
  · intro z
    obtain ⟨q, hq⟩ := e.surjective (Submodule.Quotient.mk z)
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (K • (⊤ : Submodule A T)) q
    refine ⟨x, htinj ?_⟩
    exact (he x).symm.trans hq

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open scoped TensorProduct in
/-- The affine-chart pullback unit is naturally the tensor scalar-extension unit.
Source: Stacks Project, Tags 01I9 and 01IA; Tag 088B, affine base-change paragraph.

Proof: Let g be Spec of the algebra map followed by the inverse affine-chart
isomorphism and the open immersion. The inverse image of U under g is top.
Evaluate the tensor-pullback adjunction unit on U and restrict to top; transport
its scalars along the canonical global-section isomorphism of Spec R. The chart
square identifies its B action with the specified algebra map B to R, so this
is a B-linear map for every module sheaf. Naturality follows from unit naturality
and restriction naturality. For a quasi-coherent sheaf, apply the affine pullback
sections comparison to U and the top affine open of Spec R. Transport the second
factor through the Spec global-section isomorphism and swap the tensor factors.
The resulting bijective B-linear map gives e; its pure-tensor formula at 1 says
that e carries 1 tensor x to the component of the natural comparison.
This uses no Noetherian or torsion assumption. It also applies to the empty affine
chart and to the zero algebra, since the affine-section comparison includes them. -/
private theorem affineSpec_tensor_sections_comparison
    {Y : Scheme.{u}} (U : Y.affineOpens)
    (R : Type u) [CommRing R] [Algebra Γ(Y, U.1) R] :
    let B := Γ(Y, U.1)
    let S := Spec (CommRingCat.of R)
    let g : S ⟶ Y := Spec.map (CommRingCat.ofHom (algebraMap B R)) ≫
      U.2.isoSpec.inv ≫ U.1.ι
    let T := Scheme.Modules.tensorPullback g
    let E := moduleSpecΓFunctor (R := CommRingCat.of R)
    let L := ModuleCat.restrictScalars (algebraMap B R)
    ∃ c : SheafOfModules.evaluation Y.ringCatSheaf (op U.1) ⟶ T ⋙ E ⋙ L,
      ∀ (M : Y.Modules) (_ : M.IsQuasicoherent),
        ∃ e : (R ⊗[B] Γ(M, U.1)) ≃ₗ[B] ((T ⋙ E ⋙ L).obj M),
          ∀ x : Γ(M, U.1), c.app M x = e ((1 : R) ⊗ₜ[B] x) := by
  classical
  dsimp only
  let B := Γ(Y, U.1)
  let S := Spec (CommRingCat.of R)
  let f := Spec.map (CommRingCat.ofHom (algebraMap B R))
  let g : S ⟶ Y := f ≫ U.2.fromSpec
  have hUV : (⊤ : S.Opens) ≤ g ⁻¹ᵁ U.1 := by
    simp [g, U.2.fromSpec_preimage_self]
  have hchart : U.2.fromSpec.appLE U.1 ⊤ U.2.fromSpec_preimage_self.ge =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv := by
    simp only [Scheme.Hom.appLE, U.2.fromSpec_app_self]
    simp
    rfl
  have hring : g.appLE U.1 ⊤ hUV =
      CommRingCat.ofHom (algebraMap B R) ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).inv := by
    rw [← Scheme.Hom.appLE_comp_appLE f U.2.fromSpec U.1 ⊤ ⊤
      U.2.fromSpec_preimage_self.ge (by simp)]
    rw [hchart]
    exact (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap B R))).symm
  let T := Scheme.Modules.tensorPullback g
  let P := T ⋙ moduleSpecΓFunctor (R := CommRingCat.of R) ⋙
    ModuleCat.restrictScalars (algebraMap B R)
  let adj := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)
  let unit (M : Y.Modules) : Γ(M, U.1) → Γ(T.obj M, g ⁻¹ᵁ U.1) :=
    fun x ↦ (adj.unit.app M).val.app (op U.1) x
  let c₀ (M : Y.Modules) : Γ(M, U.1) →ₗ[B] P.obj M :=
    { toFun := fun x ↦ (T.obj M).presheaf.map (homOfLE hUV).op (unit M x)
      map_add' := by
        intro x y
        dsimp only [unit]
        rw [((adj.unit.app M).val.app (op U.1)).hom.map_add]
        exact ((T.obj M).presheaf.map (homOfLE hUV).op).hom.map_add _ _
      map_smul' := by
        intro a x
        dsimp only [unit]
        rw [((adj.unit.app M).val.app (op U.1)).hom.map_smul]
        change (T.obj M).presheaf.map (homOfLE hUV).op
          ((g.app U.1).hom a • unit M x) = _
        rw [Scheme.Modules.map_smul]
        change (g.appLE U.1 ⊤ hUV) a • _ = _
        rw [hring]
        rfl }
  let c : SheafOfModules.evaluation Y.ringCatSheaf (op U.1) ⟶ P :=
    { app := fun M ↦ ModuleCat.ofHom (R := B) (X := Γ(M, U.1))
        (Y := P.obj M) (c₀ M)
      naturality := by
        intro M N a
        ext x
        have hn := adj.unit_naturality a
        have hv := congrArg (fun q ↦ q.val.app (op U.1) x) hn
        have hr := (T.map a).val.naturality (homOfLE hUV).op
        have hr' := congrArg (fun q ↦ q (unit M x)) hr
        change c₀ N (a.val.app (op U.1) x) = (T.map a).app ⊤ (c₀ M x)
        exact (hr'.trans (congrArg (fun z ↦
          (T.obj N).presheaf.map (homOfLE hUV).op z) hv)).symm }
  refine ⟨c, ?_⟩
  intro M hM
  let ρ := CommRingCat.ofHom (algebraMap B R) ≫
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv
  let : Algebra B Γ(S, ⊤) := ρ.hom.toAlgebra
  let : Module B Γ(T.obj M, ⊤) := Module.compHom _ ρ.hom
  have hc := Scheme.Modules.exists_tensorPullback_affine_sections g U
    ⟨⊤, isAffineOpen_top S⟩ hUV
  rw [hring] at hc
  obtain ⟨d, hd, _, hdt, _⟩ := hc
  let eR : R ≃ₗ[B] Γ(S, ⊤) :=
    { (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.toAddEquiv with
      map_smul' := by
        intro a r
        change (Scheme.ΓSpecIso (CommRingCat.of R)).inv (a • r) =
          ρ a * (Scheme.ΓSpecIso (CommRingCat.of R)).inv r
        rw [Algebra.smul_def]
        rw [map_mul]
        rfl }
  let eT := TensorProduct.comm B R Γ(M, U.1) ≪≫ₗ
    TensorProduct.congr (LinearEquiv.refl B Γ(M, U.1)) eR
  let d' : (R ⊗[B] Γ(M, U.1)) →ₗ[B] P.obj M :=
    { toFun := fun t ↦ d M hM (eT t)
      map_add' := by intros; simp
      map_smul' := by
        intro a t
        rw [LinearEquiv.map_smul, LinearMap.map_smul]
        rfl }
  let e := LinearEquiv.ofBijective d' ((hd M hM).comp eT.bijective)
  refine ⟨e, ?_⟩
  intro x
  change c₀ M x = d M hM (eT ((1 : R) ⊗ₜ[B] x))
  simp only [eT, LinearEquiv.trans_apply, TensorProduct.comm_tmul,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply]
  have h1 : eR (1 : R) = 1 := map_one (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  rw [h1, hdt, one_smul]
  rfl

/-- A natural comparison on all module sheaves is invertible on quasi-coherent
sheaves whose affine sections are killed by a positive power of the completion ideal.
This statement concerns one sheaf at a time, without formal systems or transitions.

Source: Stacks Project, Tags 088B (completed base change), 05GG (completion quotient),
and 01I9 (affine pullback).
(blueprint: lem-weil-pbc-completed-affine-sections-power-torsion)

Proof: Define the comparison by the unit of tensor pullback followed by restriction
from the inverse image of U to the whole completed affine scheme. This inverse image
is the whole scheme, since g factors through U. The structure-ring map on this chart
is B to its K-adic completion R; the Spec global-section identification therefore
makes the comparison B-linear. Naturality follows from the adjunction unit and
restriction maps. For a quasi-coherent sheaf M, affine pullback sections identify
this map with m mapping to 1 tensor m. If K^(n+1) kills M(U), its scalar action factors
through B/K^(n+1). Since B is Noetherian, K is finitely generated, and the positive
power completion quotient is R/K^(n+1)R = B/K^(n+1), compatibly with B to R. Tensoring
M(U) over this quotient identifies the unit with the identity, hence it is bijective
and gives an isomorphism of B-modules. The unit ideal forces M(U) = 0; the zero ideal
makes completion the original ring. The zero ring and empty affine open are included.
-/
theorem completedAffineSections_powerTorsion
    {Y : Scheme.{u}} [IsNoetherian Y] (J : Y.IdealSheafData) (U : Y.affineOpens) :
    let B := Γ(Y, U.1)
    let R := AdicCompletion (J.ideal U) B
    let S := Spec (CommRingCat.of R)
    let g : S ⟶ Y := Spec.map (CommRingCat.ofHom (algebraMap B R)) ≫
      U.2.isoSpec.inv ≫ U.1.ι
    let T := Scheme.Modules.tensorPullback g
    let E := moduleSpecΓFunctor (R := CommRingCat.of R)
    let L := ModuleCat.restrictScalars (algebraMap B R)
    ∃ c : SheafOfModules.evaluation Y.ringCatSheaf (op U.1) ⟶ T ⋙ E ⋙ L,
      ∀ (M : Y.Modules) (_ : M.IsQuasicoherent) (n : ℕ),
        J.ideal U ^ (n + 1) • (⊤ : Submodule B Γ(M, U.1)) = ⊥ →
          IsIso (c.app M) := by
  dsimp only
  let B := Γ(Y, U.1)
  let R := AdicCompletion (J.ideal U) B
  obtain ⟨c, hc⟩ := affineSpec_tensor_sections_comparison U R
  refine ⟨c, ?_⟩
  intro M hM n hzero
  obtain ⟨e, he⟩ := hc M hM
  have hB : IsNoetherianRing B := IsLocallyNoetherian.component_noetherian U
  have hu := adic_tensor_unit_bijective (J.ideal U)
    (IsNoetherian.noetherian (J.ideal U)) (ModuleCat.of B Γ(M, U.1)) (n + 1) hzero
  apply (ConcreteCategory.isIso_iff_bijective (c.app M)).mpr
  constructor
  · intro x y hxy
    apply hu.1
    apply e.injective
    exact (he x).symm.trans (hxy.trans (he y))
  · intro z
    obtain ⟨t, rfl⟩ := e.surjective z
    obtain ⟨x, hx⟩ := hu.2 t
    exact ⟨x, (he x).trans (congrArg e hx)⟩

end AlgebraicGeometry
