/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.TensorProduct.Basic
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
import WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde

/-! # Tensor coordinates for the two sides of affine base change

Source: Stacks Project, Schemes, Lemma 01I9 and Cohomology of Schemes, Lemma 02KG.
(blueprint: lem-weil-pbc-affine-base-change-tensor-comparisons).
-/

@[expose] public section

universe u
open CategoryTheory Opposite TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem tensorTildeSections (A C : Type u) [CommRing A] [CommRing C]
    [Algebra A C] (N : ModuleCat.{u} A) :
    ∃ e : C ⊗[A] N ≃ₗ[C]
        (moduleSpecΓFunctor (R := .of C)).obj
          ((tensorPullback (Spec.map (CommRingCat.ofHom (algebraMap A C)))).obj
            (tilde (R := .of A) N)),
      ∀ n : N, e ((1 : C) ⊗ₜ[A] n) =
        ((Classical.choose (exists_tensorPullbackAdjunction
          (Spec.map (CommRingCat.ofHom (algebraMap A C))))).unit.app
            (tilde (R := .of A) N)).app ⊤ (tilde.toOpen (R := .of A) N ⊤ n) := by
  obtain ⟨θ, hθ⟩ := exists_tensorPullback_tilde_iso
    (CommRingCat.ofHom (algebraMap A C))
  let E := (ModuleCat.extendScalars (algebraMap A C)).obj N
  let e := ModuleCat.tensorEquivExtendScalars A C N ≪≫ₗ
    (tilde.isoTop (R := .of C) E).toLinearEquiv ≪≫ₗ
      ((moduleSpecΓFunctor (R := .of C)).mapIso (θ.app N)).toLinearEquiv.symm
  refine ⟨e, ?_⟩
  intro n
  apply (((moduleSpecΓFunctor (R := .of C)).mapIso (θ.app N)).toLinearEquiv).injective
  change ((moduleSpecΓFunctor (R := .of C)).mapIso (θ.app N)).toLinearEquiv
    (((moduleSpecΓFunctor (R := .of C)).mapIso (θ.app N)).toLinearEquiv.symm
    ((tilde.isoTop (R := .of C) E).toLinearEquiv
      (ModuleCat.tensorEquivExtendScalars A C N ((1 : C) ⊗ₜ[A] n)))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact (hθ N n).symm

private theorem tensorQCSections (A C : Type u) [CommRing A] [CommRing C]
    [Algebra A C] (F : (Spec (.of A)).Modules) [F.IsQuasicoherent] :
    ∃ e : C ⊗[A] (moduleSpecΓFunctor (R := .of A)).obj F ≃ₗ[C]
        (moduleSpecΓFunctor (R := .of C)).obj
          ((tensorPullback (Spec.map (CommRingCat.ofHom (algebraMap A C)))).obj F),
      ∀ n : (moduleSpecΓFunctor (R := .of A)).obj F, e ((1 : C) ⊗ₜ[A] n) =
        ((Classical.choose (exists_tensorPullbackAdjunction
          (Spec.map (CommRingCat.ofHom (algebraMap A C))))).unit.app F).app ⊤ n := by
  obtain ⟨e, he⟩ := tensorTildeSections A C ((moduleSpecΓFunctor (R := .of A)).obj F)
  have : IsIso (fromTildeΓ (R := .of A) F) := isIso_fromTildeΓ_of_isQuasicoherent (R := .of A) F
  let i := (moduleSpecΓFunctor (R := .of C)).mapIso
    ((tensorPullback (Spec.map (CommRingCat.ofHom (algebraMap A C)))).mapIso
      (asIso (fromTildeΓ (R := .of A) F)))
  refine ⟨e ≪≫ₗ i.toLinearEquiv, ?_⟩
  intro n
  change i.toLinearEquiv (e ((1 : C) ⊗ₜ[A] n)) = _
  rw [he]
  have h := congr($((Classical.choose (exists_tensorPullbackAdjunction
    (Spec.map (CommRingCat.ofHom (algebraMap A C))))).unit.naturality
      (fromTildeΓ (R := .of A) F)).app ⊤ (tilde.toOpen (R := .of A)
        ((moduleSpecΓFunctor (R := .of A)).obj F) ⊤ n))
  exact h.symm.trans (congrArg
    (((Classical.choose (exists_tensorPullbackAdjunction
      (Spec.map (CommRingCat.ofHom (algebraMap A C))))).unit.app F).app ⊤)
      (fromTildeΓ_app_toOpen (R := .of A) F n))

/-- Tensor coordinates for the source and target, normalized by the pullback units.
Source: Stacks Project, Schemes, Lemma 01I9 (1),(2), and Cohomology of Schemes, Lemma 02KG.
(blueprint: lem-weil-pbc-affine-base-change-tensor-comparisons).
Proof: Pushforward of tilde along Spec of R to B is tilde of restriction of scalars,
with the same global sections and canonical section m. Compose its pullback with the
unit-compatible pullback-tilde isomorphism and the tilde global-sections unit to get a.
For b, apply the pullback-tilde comparison to B to R' tensor B, take global sections,
and restrict scalars along R' to R' tensor B. Both comparisons are isomorphisms by
01I9 and the tilde-Gamma adjunction. Their unit formulas give the first equation and
b.symm(((1 tensor 1) tensor z*m)) = eta(tilde.toOpen(z*m)). The balancing relation
over B identifies ((1 tensor z) tensor m) with ((1 tensor 1) tensor z*m), giving the
second equation. These constructions work also for the zero rings and zero module. -/
theorem exists_affineBaseChange_tensorComparisons
    (R B R' : Type u) [CommRing R] [CommRing B] [CommRing R']
    [Algebra R B] [Algebra R R'] (M : ModuleCat.{u} B) :
    letI : Module R M := Module.compHom M (algebraMap R B)
    letI : Algebra B (R' ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
    ∃ (a : ((moduleSpecΓFunctor (R := .of R')).obj
        ((tensorPullback (Spec.map (CommRingCat.ofHom (algebraMap R R')))).obj
          ((pushforward (Spec.map (CommRingCat.ofHom (algebraMap R B)))).obj
            (tilde (R := .of B) M)))) ≃ₗ[R'] R' ⊗[R] M)
      (b : ((moduleSpecΓFunctor (R := .of R')).obj
        ((pushforward (Spec.map (CommRingCat.ofHom (algebraMap R' (R' ⊗[R] B))))).obj
          ((tensorPullback (Spec.map (CommRingCat.ofHom (algebraMap B (R' ⊗[R] B))))).obj
            (tilde (R := .of B) M)))) ≃ₗ[R'] (R' ⊗[R] B) ⊗[B] M),
      (∀ m : M, a.symm ((1 : R') ⊗ₜ[R] m) =
        (((Classical.choose (exists_tensorPullbackAdjunction
            (Spec.map (CommRingCat.ofHom (algebraMap R R'))))).unit.app
          ((pushforward (Spec.map (CommRingCat.ofHom (algebraMap R B)))).obj
            (tilde (R := .of B) M))).val.app (op ⊤)
            (tilde.toOpen (R := .of B) M ⊤ m) :
          (moduleSpecΓFunctor (R := .of R')).obj
            ((tensorPullback (Spec.map (CommRingCat.ofHom (algebraMap R R')))).obj
              ((pushforward (Spec.map (CommRingCat.ofHom (algebraMap R B)))).obj
                (tilde (R := .of B) M))))) ∧
      (∀ (z : B) (m : M), b.symm (((1 : R') ⊗ₜ[R] z) ⊗ₜ[B] m) =
        (((Classical.choose (exists_tensorPullbackAdjunction
            (Spec.map (CommRingCat.ofHom (algebraMap B (R' ⊗[R] B)))))).unit.app
          (tilde (R := .of B) M)).val.app (op ⊤)
            (tilde.toOpen (R := .of B) M ⊤ (z • m)) :
          (moduleSpecΓFunctor (R := .of R')).obj
            ((pushforward (Spec.map (CommRingCat.ofHom (algebraMap R' (R' ⊗[R] B))))).obj
              ((tensorPullback (Spec.map (CommRingCat.ofHom (algebraMap B (R' ⊗[R] B))))).obj
                (tilde (R := .of B) M))))) := by
    let : Module R M := Module.compHom M (algebraMap R B)
    let : Algebra B (R' ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
    let f := Spec.map (CommRingCat.ofHom (algebraMap R B))
    let F := (pushforward f).obj (tilde (R := .of B) M)
    have : IsIso (fromTildeΓ (R := .of B) (tilde (R := .of B) M)) :=
      isIso_fromTildeΓ_of_isQuasicoherent (R := .of B) _
    have : IsIso (fromTildeΓ (R := .of R) F) := isIso_fromTildeΓ_pushforward
      (CommRingCat.ofHom (algebraMap R B)) _
    have : F.IsQuasicoherent :=
      (isQuasicoherent_iff_isIso_fromTildeΓ (R := .of R) F).mpr inferInstance
    obtain ⟨e, he⟩ := tensorQCSections R R' F
    let j := ((ModuleCat.restrictScalars (algebraMap R B)).mapIso
      (tilde.isoTop (R := .of B) M)) ≪≫
        ((pushforwardSpecMapCompΓIso (CommRingCat.ofHom (algebraMap R B))).app
          (tilde (R := .of B) M)).symm
    let d := TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R' R') j.toLinearEquiv
    let a := (d ≪≫ₗ e).symm
    let D := R' ⊗[R] B
    obtain ⟨e₂, he₂⟩ := tensorTildeSections B D M
    let k := (pushforwardSpecMapCompΓIso
      (CommRingCat.ofHom (algebraMap R' D))).app
        ((tensorPullback (Spec.map (CommRingCat.ofHom (algebraMap B D)))).obj
          (tilde (R := .of B) M))
    let e₂r := (ModuleCat.restrictScalars (algebraMap R' D)).mapIso e₂.toModuleIso
    let i : (ModuleCat.restrictScalars (algebraMap R' D)).obj
        (ModuleCat.of D (D ⊗[B] M)) ≃ₗ[R'] D ⊗[B] M :=
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun r x ↦ by
          change algebraMap R' D r • (show D ⊗[B] M from x) =
            r • (show D ⊗[B] M from x)
          exact IsScalarTower.algebraMap_smul (M := D ⊗[B] M) D r
            (show D ⊗[B] M from x)
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    let b := k.toLinearEquiv ≪≫ₗ e₂r.toLinearEquiv.symm ≪≫ₗ i
    refine ⟨a, b, ?_, ?_⟩
    · intro m
      change e (d ((1 : R') ⊗ₜ[R] m)) = _
      change e ((1 : R') ⊗ₜ[R] (tilde.toOpen (R := .of B) M ⊤ m)) = _
      exact he _
    · intro z m
      have hz : ((1 : R') ⊗ₜ[R] z) ⊗ₜ[B] m =
          (1 : D) ⊗ₜ[B] (z • m) := by
        rw [← TensorProduct.smul_tmul]
        congr 1
        change (1 : R') ⊗ₜ[R] z = z • ((1 : R') ⊗ₜ[R] (1 : B))
        simp only [Algebra.smul_def, Algebra.TensorProduct.right_algebraMap_apply,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      rw [hz]
      change e₂ ((1 : D) ⊗ₜ[B] (z • m)) = _
      exact he₂ _
end
end AlgebraicGeometry.Scheme.Modules
