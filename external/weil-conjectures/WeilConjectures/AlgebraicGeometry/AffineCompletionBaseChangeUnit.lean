/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.AdicCompletion.Algebra

import WeilConjectures.AlgebraicGeometry.AffineFormalQuotientComparison
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-! # Affine formal gluing comparison

Source: Stacks Project, Tags 087W, 0888 and 0889(1).
(blueprint: lem-weil-pbc-affine-completion-baseChange-unit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

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

-- The component proof unfolds quotient maps through two composite functors.
set_option backward.isDefEq.respectTransparency false in
/-- Extension along the adic completion leaves every positive sheaf quotient unchanged.
The source module need not be finite.

Source: Stacks Project, Tags 05GG, 087W and 0889(1).
(blueprint: lem-weil-pbc-affine-completion-baseChange-unit).

Proof: for every positive n the completion projection identifies A/I^n with
S/I^n S. Right exactness of tensor therefore identifies T/I^n T with
(S ⊗ T)/I^n(S ⊗ T), via the map x ↦ 1 ⊗ x, for an arbitrary module T.
Exactness of tilde identifies these module quotients with the sheaf quotients,
and pullback along X ≅ Spec A transports the ideal of global sections to J.
Thus each component of the displayed natural transformation is an isomorphism.
A natural transformation with invertible components is itself invertible. No
completion-as-tensor assertion about the possibly infinite T is used. For I=A
all quotients are zero; for I=0 the completion ring and unit map are the identity.
The zero ring and empty spectrum obey the same quotient argument.
-/
theorem affine_completion_baseChange_unit
    {X : Scheme.{u}} [IsNoetherian X] [IsAffine X] (J : X.IdealSheafData) :
    let A := Γ(X, ⊤)
    let I := J.ideal ⟨⊤, isAffineOpen_top X⟩
    let S := AdicCompletion I A
    let L := tilde.functor A ⋙ Scheme.Modules.pullback X.isoSpec.hom
    let C := L ⋙ formalCompletionFunctor J
    ∀ T : ModuleCat.{u} A,
      IsIso (C.map (ModuleCat.ofHom (TensorProduct.mk A S T (1 : S)))) := by
  dsimp only
  intro T
  let A := Γ(X, ⊤)
  let I := J.ideal ⟨⊤, isAffineOpen_top X⟩
  let S := AdicCompletion I A
  let L := tilde.functor A ⋙ Scheme.Modules.pullback X.isoSpec.hom
  let N := ModuleCat.of A (S ⊗[A] T)
  let f : T ⟶ N := ModuleCat.ofHom (TensorProduct.mk A S T (1 : S))
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro k
  let n := k.unop + 1
  have : IsNoetherianRing A :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  obtain ⟨e, he⟩ := adic_tensor_unit_quotient I (IsNoetherian.noetherian I) T n
  obtain ⟨a, ha⟩ := affine_formalQuotient_comparison J T n (Nat.succ_pos _)
  obtain ⟨b, hb⟩ := affine_formalQuotient_comparison J N n (Nat.succ_pos _)
  let fQ := (I ^ n • (⊤ : Submodule A T)).mapQ
    (I ^ n • (⊤ : Submodule A N)) f.hom (Submodule.smul_top_le_comap_smul_top _ _)
  have hfQ : fQ = e.toLinearMap := by
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    exact (he x).symm
  have : IsIso (ModuleCat.ofHom fQ) := by
    rw [hfQ]
    exact (e.toModuleIso).isIso_hom
  let q := formalModuleQuotientMap J (L.map f) (Nat.le_refl n)
  have : Epi (formalModuleQuotientπ J n (L.obj T)) := by
    dsimp [formalModuleQuotientπ]
    infer_instance
  have hq : q ≫ b.hom = a.hom ≫ L.map (ModuleCat.ofHom fQ) := by
    apply (cancel_epi (formalModuleQuotientπ J n (L.obj T))).1
    rw [← Category.assoc]
    have hπ : formalModuleQuotientπ J n (L.obj T) ≫ q =
        L.map f ≫ formalModuleQuotientπ J n (L.obj N) := by
      exact cokernel.π_desc _ _ _
    rw [hπ, Category.assoc, hb, ← L.map_comp, ← Category.assoc, ha, ← L.map_comp]
    congr 1
  have hq' : q = a.hom ≫ L.map (ModuleCat.ofHom fQ) ≫ b.inv := by
    rw [← Category.assoc, ← hq, Category.assoc, b.hom_inv_id, Category.comp_id]
  change IsIso q
  rw [hq']
  infer_instance

end AlgebraicGeometry
