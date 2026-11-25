/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Algebra.Category.Ring.Constructions

/-! # Tensor sections on the inverse-image affine chart

Source: Stacks Project, Schemes Tags 01I4, 01IA, 01HV.
(blueprint: lem-pc-affine-pullback-chart-tensor-sections).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse image of an affine open under an affine base change is affine, and
its actual pullback-module sections are the scalar extension of the original sections.
Source: Stacks Project, Schemes Tags 01I4, 01IA, 01HV.
(blueprint: lem-pc-affine-pullback-chart-tensor-sections).

Proof: Put B = O_X(U), N = M(U). Restrict the cartesian square to U. Identifying U
with Spec B and Y with Spec T by e identifies the inverse image W with
Spec(B tensor_A T); he ensures that the second structure map is induced by q.
Thus W is affine. The affine pullback sections comparison identifies G(W) with
N tensor_B (B tensor_A T), with its ordinary section action. Swap the factors and
reassociate to obtain T tensor_A N. On pure tensors the forward comparison sends
t tensor n to t times the pulled-back section n. Its inverse sends
n tensor (b tensor t) to t tensor (b*n). The balancing relations give well-defined
maps and their two composites are identities by tensor induction. Compatibility
with the second projection identifies the T-action with the composite of the
canonical Spec-sections map, e.hom.appTop, and the second projection on sections.
Empty U gives the zero ring and zero sections; the formulas remain valid for
zero T and zero N. No flatness or finite presentation is used. -/
theorem exists_affine_pullback_chart_tensor_sections
    (A T : CommRingCat.{u}) {X Y : Scheme.{u}} (f : X ⟶ Spec A)
    (M : X.Modules) [M.IsQuasicoherent] (U : X.affineOpens)
    (q : A ⟶ T) (p : Y ⟶ Spec A) (e : Y ≅ Spec T)
    (he : e.hom ≫ Spec.map q = p) :
    ∃ W : (pullback f p : Scheme.{u}).affineOpens,
      W.1 = (pullback.fst f p) ⁻¹ᵁ U.1 ∧
      (letI : Module (A : Type u) Γ(M, U.1) :=
        Module.compHom _ (((Scheme.ΓSpecIso A).inv ≫
          f.appLE ⊤ U.1 (by simp)).hom)
       letI : Algebra (A : Type u) (T : Type u) := q.hom.toAlgebra
       letI : Module (T : Type u)
           Γ((Scheme.Modules.tensorPullback (pullback.fst f p)).obj M, W.1) :=
         Module.compHom _ (((Scheme.ΓSpecIso T).inv ≫ e.hom.appTop ≫
           (pullback.snd f p).appLE ⊤ W.1 (by simp)).hom)
       Nonempty (((T : Type u) ⊗[(A : Type u)] Γ(M, U.1)) ≃ₗ[(T : Type u)]
         Γ((Scheme.Modules.tensorPullback (pullback.fst f p)).obj M, W.1)))  := by
  classical
  have : IsAffine Y := (IsAffine.iff_of_isIso e.hom).mpr inferInstance
  let a := pullback.fst f p
  let b := pullback.snd f p
  have : IsAffineHom a := MorphismProperty.pullback_fst f p (inferInstance : IsAffineHom p)
  let W : (pullback f p : Scheme.{u}).affineOpens := ⟨a ⁻¹ᵁ U.1, U.2.preimage a⟩
  refine ⟨W, rfl, ?_⟩
  let B := Γ(X, U.1)
  let C := Γ(pullback f p, W.1)
  let N := Γ(M, U.1)
  let G := (Scheme.Modules.tensorPullback a).obj M
  let P := Γ(G, W.1)
  let α : A ⟶ B := (Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ U.1 (by simp)
  let k : T ⟶ Γ(Y, ⊤) := (Scheme.ΓSpecIso T).inv ≫ e.hom.appTop
  let β : T ⟶ C := k ≫ b.appLE ⊤ W.1 (by simp)
  let γ : B ⟶ C := a.appLE U.1 W.1 le_rfl
  let : Algebra (A : Type u) B := α.hom.toAlgebra
  let : Algebra (A : Type u) (T : Type u) := q.hom.toAlgebra
  let : Algebra B C := γ.hom.toAlgebra
  let : Algebra (T : Type u) C := β.hom.toAlgebra
  let : Algebra (A : Type u) C := (γ.hom.comp α.hom).toAlgebra
  have : IsScalarTower (A : Type u) B C := IsScalarTower.of_algebraMap_eq' rfl
  let : Module (A : Type u) N := Module.compHom _ α.hom
  have : IsScalarTower (A : Type u) B N := IsScalarTower.of_compHom _ _ _
  let : Module B P := Module.compHom _ γ.hom
  let : Module (T : Type u) P := Module.compHom _ β.hom
  have : IsScalarTower B C P := IsScalarTower.of_compHom _ _ _
  have : IsScalarTower (T : Type u) C P := IsScalarTower.of_compHom _ _ _
  have H := IsPullback.of_hasPullback f p
  have hp := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U.1)
    (UY := W.1) (by simp) (by simp) (by simp [W, a])).mp
      (isIso_pushoutSection_of_isAffineOpen H (by simp) (by simp) (by simp [W, a])
        (isAffineOpen_top _) (isAffineOpen_top _) U.2)
  have hp' : IsPushout α q γ β := by
    refine hp.of_iso (Scheme.ΓSpecIso A) (Iso.refl _) (asIso k).symm (Iso.refl _)
      ?_ ?_ ?_ ?_
    · simp [α]
    · apply (cancel_mono k).mp
      simp only [Category.assoc, Iso.symm_hom, asIso_inv, IsIso.inv_hom_id,
        Category.comp_id]
      rw [← he]
      simp [k, Scheme.Hom.appLE, Scheme.Hom.appTop]
    · simp [γ, a]
    · simp [β, b]
  have : IsScalarTower (A : Type u) (T : Type u) C := by
    apply IsScalarTower.of_algebraMap_eq'
    exact congrArg CommRingCat.Hom.hom hp'.w
  have : Algebra.IsPushout (A : Type u) B (T : Type u) C :=
    CommRingCat.isPushout_iff_isPushout.mp hp'
  have : Algebra.IsPushout (A : Type u) (T : Type u) B C := Algebra.IsPushout.symm inferInstance
  obtain ⟨c, hc, hlin, _⟩ :=
    Scheme.Modules.exists_tensorPullback_affine_sections a U W le_rfl
  let d : (C ⊗[B] N) →ₗ[C] P :=
    { toFun := fun t ↦ c M inferInstance (TensorProduct.comm B C N t)
      map_add' := by intros; simp
      map_smul' := by
        intro r t
        have h := hlin M inferInstance r (TensorProduct.comm B C N t)
        change c M _ ((TensorProduct.comm B N C).symm
          (r • (TensorProduct.comm B N C) ((TensorProduct.comm B C N) t))) = _ at h
        simpa only [TensorProduct.comm_symm, TensorProduct.comm_comm,
          RingHom.id_apply] using h }
  have hd : Function.Bijective d :=
    (hc M inferInstance).comp (TensorProduct.comm B C N).bijective
  let E := LinearEquiv.ofBijective d hd
  exact ⟨(Algebra.IsPushout.cancelBaseChange (A : Type u) (T : Type u) B C N).symm ≪≫ₗ
    E.restrictScalars (T : Type u)⟩

end AlgebraicGeometry
