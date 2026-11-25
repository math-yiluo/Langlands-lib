/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import WeilConjectures.AlgebraicGeometry.AffineTopTensorSections

/-! # Normalized affine pullback models with an isomorphic starting chart

Source: Stacks Project, Tag 01I6, Lemmas 26.7.1, 26.7.3, 26.7.4 and 26.7.5.
(blueprint: lem-pc-affine-isomorphic-source-normalized-models).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
open scoped ChangeOfRings
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The pullback unit, viewed as a linear map after restricting scalars through a
presentation of the destination section ring. -/
private noncomputable def affinePullbackSectionMap {A W : Scheme.{u}} (q : W ⟶ A)
    (M : A.Modules) (S : CommRingCat.{u}) (r : Γ(A, ⊤) →+* S)
    (ρ : S ≃+* Γ(W, ⊤)) (hρ : ∀ b, ρ (r b) = q.appTop b) :
    ModuleCat.of Γ(A, ⊤) Γ(M, ⊤) ⟶
      (ModuleCat.restrictScalars r).obj ((ModuleCat.restrictScalars ρ.toRingHom).obj
        (ModuleCat.of Γ(W, ⊤) Γ((Scheme.Modules.pullback q).obj M, ⊤))) :=
  ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars r).obj
      ((ModuleCat.restrictScalars ρ.toRingHom).obj
        (ModuleCat.of Γ(W, ⊤) Γ((Scheme.Modules.pullback q).obj M, ⊤))))
    { toFun := pullbackΓ q M
      map_add' := map_add _
      map_smul' := fun b m ↦ by
        change pullbackΓ q M (b • m) = ρ (r b) • pullbackΓ q M m
        rw [hρ, pullbackΓ_apply, pullbackΓ_apply]
        exact Scheme.Modules.Hom.app_smul _ b m }

/-- The canonical affine tensor comparison. It is constructed by the
extension/restriction adjunction, without choosing an existence witness.
On pure tensors it sends `b ⊗ m` to `ρ b • pullbackΓ q M m`. -/
private noncomputable def affinePullbackTensorMap {A W : Scheme.{u}} (q : W ⟶ A)
    (M : A.Modules) (S : CommRingCat.{u}) (r : Γ(A, ⊤) →+* S)
    (ρ : S ≃+* Γ(W, ⊤)) (hρ : ∀ b, ρ (r b) = q.appTop b) :
    (ModuleCat.extendScalars r).obj (ModuleCat.of Γ(A, ⊤) Γ(M, ⊤)) ⟶
      (ModuleCat.restrictScalars ρ.toRingHom).obj
        (ModuleCat.of Γ(W, ⊤) Γ((Scheme.Modules.pullback q).obj M, ⊤)) :=
  (ModuleCat.extendRestrictScalarsAdj r).homEquiv _ _ |>.symm
    (affinePullbackSectionMap q M S r ρ hρ)

/-- The canonical tensor comparison is bijective on affine schemes.
Source: Stacks Project, Tags 01I9 (pullback of an associated module) and
01IB (the affine quasi-coherent equivalence).

Proof: Identify A with Spec Γ(A,O_A) and W with Spec S, using their canonical
scheme-to-spectrum isomorphisms and the presentation ρ for W. Naturality of
these charts and the equation ρ(r(b)) = q.appTop(b) identify q with Spec(r).
By quasi-coherence, M is the associated sheaf of Γ(A,M) (Tag 01IB).
Its pullback along Spec(r) is the associated sheaf of S ⊗_r Γ(A,M)
(Tag 01I9). Taking global sections of the associated sheaf recovers this
module (Tag 01IB). The resulting isomorphism sends b ⊗ m to
ρ(b) times the pullback unit of m, by the unit formula of the tilde pullback
comparison. The tensor universal property therefore identifies it with the
explicit affinePullbackTensorMap above. Being this composite of isomorphisms,
that map is bijective. The argument applies to the zero ring, zero modules,
and arbitrary (not necessarily finitely presented) quasi-coherent modules. -/
private theorem affinePullbackTensorMap_bijective {A W : Scheme.{u}} [IsAffine A] [IsAffine W]
    (q : W ⟶ A) (M : A.Modules) (hMq : M.IsQuasicoherent)
    (S : CommRingCat.{u}) (r : Γ(A, ⊤) →+* S) (ρ : S ≃+* Γ(W, ⊤))
    (hρ : ∀ b, ρ (r b) = q.appTop b) :
    Function.Bijective (affinePullbackTensorMap q M S r ρ hρ) := by
  classical
  let : Algebra Γ(A, ⊤) Γ(W, ⊤) := q.appTop.hom.toAlgebra
  let R := ModuleCat.of Γ(A, ⊤) Γ(M, ⊤)
  let S₀ := (ModuleCat.restrictScalars r).obj (ModuleCat.of S S)
  let l : S₀ ≃ₗ[Γ(A, ⊤)] Γ(W, ⊤) :=
    { ρ.toAddEquiv with
      map_smul' := fun b z ↦ by
        change ρ (r b * (show S from z)) = q.appTop b * ρ (show S from z)
        rw [map_mul, hρ] }
  let e₀ := (TensorProduct.congr l (LinearEquiv.refl Γ(A, ⊤) R)) ≪≫ₗ
    TensorProduct.comm Γ(A, ⊤) Γ(W, ⊤) R
  obtain ⟨d, hd, hp⟩ := Scheme.exists_affineTopTensorSections q M hMq
    (inferInstance : IsAffine A) (inferInstance : IsAffine W)
  let adj := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction q)
  let k := adj.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction q)
  let j := ((k.hom.app M).app ⊤)
  have hj : Function.Bijective j := ConcreteCategory.bijective_of_isIso j
  have hk (m : Γ(M, ⊤)) :
      j (Scheme.Modules.tensorSectionsUnit q M m) = pullbackΓ q M m := by
    have hu := adj.unit_leftAdjointUniq_hom_app
      (Scheme.Modules.pullbackPushforwardAdjunction q) M
    have hi : (homOfLE q.preimage_top.ge) = 𝟙 (⊤ : W.Opens) := rfl
    dsimp only [Scheme.Modules.tensorSectionsUnit]
    erw [hi, op_id, ((Scheme.Modules.tensorPullback q).obj M).presheaf.map_id,
      Category.comp_id]
    rw [pullbackΓ_def]
    exact congr($(hu).app ⊤ m)
  have heq (z : (ModuleCat.extendScalars r).obj R) :
      affinePullbackTensorMap q M S r ρ hρ z = j (d (e₀ z)) := by
    induction z using TensorProduct.inductionOn with
    | tmul b₀ m =>
      let b : S := b₀
      change affinePullbackTensorMap q M S r ρ hρ (b ⊗ₜ[Γ(A, ⊤), r] m) =
        j (d (m ⊗ₜ[Γ(A, ⊤)] ρ b))
      rw [hp, Scheme.Modules.Hom.app_smul, hk]
      have hunit : affinePullbackTensorMap q M S r ρ hρ
          ((1 : S) ⊗ₜ[Γ(A, ⊤), r] m) = pullbackΓ q M m := by
        change (ModuleCat.extendRestrictScalarsAdj r).homEquiv _ _
          ((ModuleCat.extendRestrictScalarsAdj r).homEquiv _ _ |>.symm
            (affinePullbackSectionMap q M S r ρ hρ)) m = _
        rw [Equiv.apply_symm_apply]
        rfl
      have ht : b ⊗ₜ[Γ(A, ⊤), r] m =
          b • ((1 : S) ⊗ₜ[Γ(A, ⊤), r] m) := by
        rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
      rw [ht, map_smul, hunit]
      rfl
    | add z z' hz hz' => simp only [map_add, hz, hz']
  have H : Function.Bijective
      (fun z : (ModuleCat.extendScalars r).obj R ↦ j (d (e₀ z))) :=
    hj.comp (hd.comp e₀.bijective)
  have hh : (fun z ↦ affinePullbackTensorMap q M S r ρ hρ z) =
      (fun z : (ModuleCat.extendScalars r).obj R ↦ j (d (e₀ z))) := funext heq
  rw [← hh] at H
  exact H

private theorem pullbackΓ_bijective_of_isIso {A T : Scheme.{u}}
    (s : T ⟶ A) [IsIso s] (M : A.Modules) : Function.Bijective (pullbackΓ s M) := by
  rw [pullbackΓ_def]
  apply Scheme.Modules.bijective_pullbackUnit_app_of_isOpenImmersion
  intro x _
  exact (ConcreteCategory.bijective_of_isIso s.base).2 x

private theorem tensorMap_one_tmul {A W : Scheme.{u}} (q : W ⟶ A)
    (M : A.Modules) (S : CommRingCat.{u}) (r : Γ(A, ⊤) →+* S)
    (ρ : S ≃+* Γ(W, ⊤)) (hρ : ∀ b, ρ (r b) = q.appTop b) (m : Γ(M, ⊤)) :
    affinePullbackTensorMap q M S r ρ hρ ((1 : S) ⊗ₜ[Γ(A, ⊤), r] m) =
      pullbackΓ q M m := by
  change (ModuleCat.extendRestrictScalarsAdj r).homEquiv _ _
    ((ModuleCat.extendRestrictScalarsAdj r).homEquiv _ _ |>.symm
      (affinePullbackSectionMap q M S r ρ hρ)) m = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- Normalized scalar-extension models for one affine pullback, starting
from sections on an isomorphic affine chart. The starting equivalences are fixed
before the destination chart, its coefficient ring, or its ring presentation.
Source: Stacks Project, Tag 01I6, Lemmas 26.7.1, 26.7.3, 26.7.4 and 26.7.5.
(blueprint: lem-pc-affine-isomorphic-source-normalized-models).

Proof: Since s is an isomorphism, its pullback unit is bijective on global
sections. Take its inverse as δM and δN. This choice depends only on s,M,N.
Identify A and T with the spectra of their section rings, and identify W with
Spec S using ρ. The displayed ring equation says precisely that q corresponds
to r composed with s.appTop. Apply affine quasi-coherent reconstruction to M,N
and the scalar-extension/pullback identification. Changing coordinates by s
and ρ gives eM,eN. On tensors this map is b tensor m mapped to ρ(b) times the
pullback of δ(m); thus it is semilinear and has the stated unit formula. Its
inverse is the inverse affine reconstruction comparison, so it is an additive
equivalence, even for zero rings and zero modules. There is no finite-presentation
hypothesis. -/
theorem affine_isomorphic_source_normalized_models
    {A T : Scheme.{u}} [IsAffine A] (s : T ⟶ A) [IsIso s]
    (M N : A.Modules) (hMq : M.IsQuasicoherent) (hNq : N.IsQuasicoherent) :
    let P := ModuleCat.of Γ(T, ⊤) Γ((Scheme.Modules.pullback s).obj M, ⊤)
    let Q := ModuleCat.of Γ(T, ⊤) Γ((Scheme.Modules.pullback s).obj N, ⊤)
    ∃ (δM : (P : Type u) ≃ Γ(M, ⊤)) (δN : (Q : Type u) ≃ Γ(N, ⊤)),
      ∀ (W : Scheme.{u}) (_ : IsAffine W) (q : W ⟶ A)
        (S : CommRingCat.{u}) (r : Γ(T, ⊤) →+* S) (ρ : S ≃+* Γ(W, ⊤)),
        (∀ b, ρ (r (s.appTop b)) = q.appTop b) →
        ∃ (eM : (ModuleCat.extendScalars r).obj P ≃+
            Γ((Scheme.Modules.pullback q).obj M, ⊤))
          (eN : (ModuleCat.extendScalars r).obj Q ≃+
            Γ((Scheme.Modules.pullback q).obj N, ⊤)),
          (∀ b z, eM (b • z) = ρ b • eM z) ∧
          (∀ b z, eN (b • z) = ρ b • eN z) ∧
          (∀ m, eM ((1 : S) ⊗ₜ[Γ(T, ⊤), r] m) = pullbackΓ q M (δM m)) ∧
          (∀ m, eN ((1 : S) ⊗ₜ[Γ(T, ⊤), r] m) = pullbackΓ q N (δN m)) := by
  dsimp only
  let δM := (Equiv.ofBijective (pullbackΓ s M) (pullbackΓ_bijective_of_isIso s M)).symm
  let δN := (Equiv.ofBijective (pullbackΓ s N) (pullbackΓ_bijective_of_isIso s N)).symm
  refine ⟨δM, δN, ?_⟩
  intro W hW q S r ρ hρ
  let : IsAffine W := hW
  let a := s.appTop.hom
  let f := r.comp a
  have hf : ∀ b, ρ (f b) = q.appTop b := hρ
  have single (L : A.Modules) (hLq : L.IsQuasicoherent) :
      let P := ModuleCat.of Γ(T, ⊤) Γ((Scheme.Modules.pullback s).obj L, ⊤)
      let δ := (Equiv.ofBijective (pullbackΓ s L) (pullbackΓ_bijective_of_isIso s L)).symm
      ∃ e : (ModuleCat.extendScalars r).obj P ≃+
          Γ((Scheme.Modules.pullback q).obj L, ⊤),
        (∀ b z, e (b • z) = ρ b • e z) ∧
        (∀ m, e ((1 : S) ⊗ₜ[Γ(T, ⊤), r] m) = pullbackΓ q L (δ m)) := by
    dsimp only
    let R := ModuleCat.of Γ(A, ⊤) Γ(L, ⊤)
    let P := ModuleCat.of Γ(T, ⊤) Γ((Scheme.Modules.pullback s).obj L, ⊤)
    let δ := (Equiv.ofBijective (pullbackΓ s L) (pullbackΓ_bijective_of_isIso s L)).symm
    let h : R ⟶ (ModuleCat.restrictScalars a).obj P := ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars a).obj P)
      { toFun := pullbackΓ s L
        map_add' := map_add _
        map_smul' := fun b m ↦ by
          change pullbackΓ s L (b • m) = s.appTop b • pullbackΓ s L m
          rw [pullbackΓ_apply, pullbackΓ_apply]
          exact Scheme.Modules.Hom.app_smul _ b m }
    let hEquiv := LinearEquiv.ofBijective h.hom (pullbackΓ_bijective_of_isIso s L)
    let aEquiv := (asIso s.appTop).commRingCatIsoToRingEquiv
    have : (ModuleCat.restrictScalars a).IsEquivalence :=
      ModuleCat.restrictScalars_isEquivalence_of_ringEquiv aEquiv
    let i₁ : (ModuleCat.extendScalars a).obj R ≅ P :=
      (ModuleCat.extendScalars a).mapIso hEquiv.toModuleIso ≪≫
        asIso ((ModuleCat.extendRestrictScalarsAdj a).counit.app P)
    let i : (ModuleCat.extendScalars f).obj R ≅ (ModuleCat.extendScalars r).obj P :=
      (ModuleCat.extendScalarsComp a r).app R ≪≫
        (ModuleCat.extendScalars r).mapIso i₁
    have hi (m : Γ(L, ⊤)) :
        i.hom ((1 : S) ⊗ₜ[Γ(A, ⊤), f] m) =
          (1 : S) ⊗ₜ[Γ(T, ⊤), r] (pullbackΓ s L m) := by
      change (ModuleCat.extendScalars r).map i₁.hom
        (((ModuleCat.extendScalarsComp a r).hom.app R) ((1 : S) ⊗ₜ m)) = _
      rw [ModuleCat.extendScalarsComp_hom_app_one_tmul, ModuleCat.ExtendScalars.map_tmul]
      change (1 : S) ⊗ₜ[Γ(T, ⊤), r]
        (((ModuleCat.extendRestrictScalarsAdj a).counit.app P)
          (((ModuleCat.extendScalars a).map h) ((1 : Γ(T, ⊤)) ⊗ₜ m))) = _
      rw [ModuleCat.ExtendScalars.map_tmul]
      erw [ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul]
      rfl
    let c := affinePullbackTensorMap q L S f ρ hf
    let e₀ := AddEquiv.ofBijective c.hom.toAddHom
      (affinePullbackTensorMap_bijective q L hLq S f ρ hf)
    let e := i.toLinearEquiv.symm.toAddEquiv.trans e₀
    refine ⟨e, ?_, ?_⟩
    · intro b z
      change c (i.inv (b • z)) = ρ b • c (i.inv z)
      rw [map_smul, map_smul]
      rfl
    · intro m
      have hu : pullbackΓ s L (δ m) = m :=
        (Equiv.ofBijective (pullbackΓ s L) (pullbackΓ_bijective_of_isIso s L)).apply_symm_apply m
      have hv : i.inv ((1 : S) ⊗ₜ[Γ(T, ⊤), r] m) =
          (1 : S) ⊗ₜ[Γ(A, ⊤), f] (δ m) := by
        apply i.toLinearEquiv.injective
        change i.hom (i.inv ((1 : S) ⊗ₜ[Γ(T, ⊤), r] m)) =
          i.hom ((1 : S) ⊗ₜ[Γ(A, ⊤), f] (δ m))
        rw [hi, hu]
        exact i.toLinearEquiv.apply_symm_apply _
      change c (i.inv ((1 : S) ⊗ₜ[Γ(T, ⊤), r] m)) = _
      rw [hv]
      exact tensorMap_one_tmul q L S f ρ hf (δ m)
  obtain ⟨eM, heM₁, heM₂⟩ := single M hMq
  obtain ⟨eN, heN₁, heN₂⟩ := single N hNq
  exact ⟨eM, eN, heM₁, heN₁, heM₂, heN₂⟩

end AlgebraicGeometry
