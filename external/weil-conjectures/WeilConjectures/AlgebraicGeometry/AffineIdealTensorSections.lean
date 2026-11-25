/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

@[expose] public section

universe u v

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- The affine ideal tensor comparison, before identifying its source with `I/I²`.
Source: Stacks Project, Morphisms, Lemma 01R3 (2), and Schemes, Tag 01I9.
(blueprint: lem-weil-pbc-affine-ideal-tensor-sections)

Proof: Put A = Γ(X,U) and V = i⁻¹U. Since i is a closed immersion, V is affine
and A → Γ(Z,V) is surjective. The first isomorphism theorem and r identify
Γ(Z,V) with R/I. The inclusion of i.ker.toModules is injective on U and its
range is the kernel of this section map, so its sections identify with I
semilinearly along r. The ideal module is quasi-coherent: it is the kernel of
the structure-module map to the closed-subscheme pushforward, and structure
modules, closed-immersion pushforwards, and kernels are quasi-coherent.
Apply exists_tensorPullback_affine_sections to i, U, V and this ideal module.
Transport its bijective comparison along the two section identifications.
This gives the displayed semilinear equivalence on I ⊗[R] (R/I). Its formula
on a ⊗ 1 is the pure-tensor formula of the affine comparison at b = 1.
Pushforward sections on U are pullback sections on V with scalars restricted
along i.app U, which gives exactly the scalar action in the displayed target. -/
theorem affine_ideal_tensor_sections {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] :
      ∀ (U : X.affineOpens) (R : Type v) [CommRing R]
        (r : R ≃+* Γ(X, U.1)) (I : Ideal R),
        I = RingHom.ker ((i.app U.1).hom.comp (r : R →+* Γ(X, U.1))) →
        ∃ e : LinearEquiv (r : R →+* Γ(X, U.1))
            (σ' := (r.symm : Γ(X, U.1) →+* R)) (I ⊗[R] (R ⧸ I))
            Γ((pushforward i).obj ((tensorPullback i).obj i.ker.toModules), U.1),
          ∀ (a : I) (s : Γ(i.ker.toModules, U.1)),
            i.ker.toModulesι.app U.1 s = r (a : R) →
            e (a ⊗ₜ[R] (1 : R ⧸ I)) =
              ((Classical.choose (exists_tensorPullbackAdjunction i)).unit.app
                i.ker.toModules).app U.1 s :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  by
    classical
    intro U R _ r I hI
    subst I
    let A := Γ(X, U.1)
    let V : Z.affineOpens := ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩
    let B := Γ(Z, V.1)
    let ρ : R →+* B := (i.app U.1).hom.comp (r : R →+* A)
    let I := RingHom.ker ρ
    have hρ : Function.Surjective ρ := (i.app_surjective U.1 U.2).comp r.surjective
    have hrange : Set.range (i.ker.toModulesι.app U.1) =
        (RingHom.ker (i.app U.1).hom : Set A) := by
      rw [i.ker.range_toModulesι_app U, i.ker_apply U]
    let d : Γ(i.ker.toModules, U.1) →ₛₗ[(r.symm : A →+* R)] I :=
      { toFun := fun s ↦ ⟨r.symm (i.ker.toModulesι.app U.1 s), by
          change (i.app U.1) (r (r.symm (i.ker.toModulesι.app U.1 s))) = 0
          rw [r.apply_symm_apply]
          exact (Set.ext_iff.mp hrange _).mp ⟨s, rfl⟩⟩
        map_add' := by
          intro s t
          apply Subtype.ext
          simp
        map_smul' := by
          intro a s
          apply Subtype.ext
          change r.symm ((i.ker.toModulesι.val.app (Opposite.op U.1)).hom (a • s)) = _
          rw [LinearMap.map_smul]
          exact r.symm.map_mul _ _ }
    have hd : Function.Bijective d := by
      constructor
      · intro s t h
        apply i.ker.injective_toModulesι_app U.1
        exact r.symm.injective (congrArg Subtype.val h)
      · intro a
        have ha : (r (a : R)) ∈ RingHom.ker (i.app U.1).hom := a.2
        obtain ⟨s, hs⟩ := (Set.ext_iff.mp hrange _).mpr ha
        refine ⟨s, Subtype.ext ?_⟩
        change r.symm (i.ker.toModulesι.app U.1 s) = (a : R)
        rw [hs, r.symm_apply_apply]
    let eI : LinearEquiv (r : R →+* A) (σ' := (r.symm : A →+* R))
        I Γ(i.ker.toModules, U.1) := (LinearEquiv.ofBijective d hd).symm
    have heI (a : I) : i.ker.toModulesι.app U.1 (eI a) = r (a : R) := by
      have h := congrArg Subtype.val ((LinearEquiv.ofBijective d hd).apply_symm_apply a)
      exact r.symm.injective (h.trans (r.symm_apply_apply _).symm)
    let q : (R ⧸ I) ≃+* B := RingHom.quotientKerEquivOfSurjective hρ
    let : Algebra A B := (i.app U.1).hom.toAlgebra
    let eB : LinearEquiv (r : R →+* A) (σ' := (r.symm : A →+* R)) (R ⧸ I) B :=
      { q.toAddEquiv with
        map_smul' := by
          intro a b
          obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
          change q (Ideal.Quotient.mk I (a * b)) = (i.app U.1) (r a) * q _
          simp only [q, map_mul]
          rfl }
    have hqc : i.ker.toModules.IsQuasicoherent := by
      have := SheafOfModules.isQuasicoherent_unit (R := i.ker.subscheme.ringCatSheaf)
      have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
      have h := isQuasicoherent_pushforward_of_isClosedImmersion i.ker.subschemeι
        (SheafOfModules.unit i.ker.subscheme.ringCatSheaf)
      have : ((SheafOfModules.pushforward i.ker.subschemeι.toRingCatSheafHom).obj
          (SheafOfModules.unit i.ker.subscheme.ringCatSheaf)).IsQuasicoherent := h
      exact isQuasicoherent_kernel i.ker.toPushforwardSubscheme
    have hcomp := exists_tensorPullback_affine_sections i U V le_rfl
    dsimp only at hcomp
    rw [show i.appLE U.1 V.1 le_rfl = i.app U.1 from i.appLE_eq_app] at hcomp
    obtain ⟨c, hc, _, hp, _⟩ := hcomp
    let : Module A Γ((tensorPullback i).obj i.ker.toModules, V.1) :=
      Module.compHom _ (i.app U.1).hom
    let c' : (Γ(i.ker.toModules, U.1) ⊗[A] B) ≃ₗ[A]
        Γ((pushforward i).obj ((tensorPullback i).obj i.ker.toModules), U.1) :=
      LinearEquiv.ofBijective (c i.ker.toModules hqc) (hc i.ker.toModules hqc)
    refine ⟨(TensorProduct.congr eI eB).trans c', ?_⟩
    intro a s hs
    have has : eI a = s := i.ker.injective_toModulesι_app U.1 ((heI a).trans hs.symm)
    change c' (TensorProduct.congr eI eB (a ⊗ₜ[R] (1 : R ⧸ I))) = _
    rw [TensorProduct.congr_tmul, has]
    have heB : eB (1 : R ⧸ I) = (1 : B) := q.map_one
    rw [heB]
    change c i.ker.toModules hqc (s ⊗ₜ[A] (1 : B)) = _
    rw [hp]
    simp only [homOfLE_refl, op_id, Functor.id_obj, Functor.comp_obj, Functor.op_obj,
      one_smul, pushforward_obj_obj]
    exact congrArg (fun k ↦ k
      (((Classical.choose (exists_tensorPullbackAdjunction i)).unit.app
        i.ker.toModules).app U.1 s))
      (((tensorPullback i).obj i.ker.toModules).presheaf.map_id (Opposite.op V.1))

end AlgebraicGeometry.Scheme.Modules
