/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.RingTheory.AdicCompletion.Algebra
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleCompletedProjectionsLinear
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleStabilizedKernelSectionRange

/-! # Affine section quotients of stabilized formal kernels

Source: Stacks Project, Tags 087W and 087X, affine calculation for claim (a).
(blueprint: lem-weil-pbc-formal-kernel-affine-section-quotients).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Stabilized formal kernel sections are compatible quotients of one completed submodule.

Source: Stacks Project, Lemma 087X (lemma-inverse-systems-abelian), calculation of
K prime_m, using Lemma 087W (lemma-inverse-systems-affine).
(blueprint: lem-weil-pbc-formal-kernel-affine-section-quotients).

Proof: Restrict both formal systems and their map to U, and transport along U's
canonical isomorphism with Spec Gamma(U,O_X). The affine formal-module equivalence
gives finite completed modules N and P, a completed-linear map f, and compatible
surjective A-linear projections with kernels K^(m+1)N and K^(m+1)P. Put L = ker f.
The reduced-kernel image bound supplies a. At level l = max(m+c,m+a), the image
of the finite-level kernel in N/K^(m+1)N equals the image of L. Stabilization hc
identifies this with the image at m+c. Affine sections preserve kernels and images
of quasi-coherent modules, so hS identifies this image with Gamma(U,S_m).
Restriction of the projection to L followed by this identification defines q_m;
it is surjective and its zero criterion is membership in K^(m+1)N. The components
of j are monic by hS. Apply naturality of j to q_b(z) and cancel j_a on sections
to obtain transition compatibility for every a <= b.
No stalks, localized submodule order maps, or intersection bounds are constructed.
Empty U, zero modules, and zero or unit ideals obey the same quotient formulas. -/
theorem coherentFormalModule_kernel_affine_section_quotients
    {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F H : CoherentFormalModule X I) (α : F ⟶ H)
    (c : ℕ) (S : ℕᵒᵖ ⥤ X.Modules) (j : S ⟶ F.obj)
    (hc : ∀ (l m : ℕ) (h : m + c ≤ l),
      Subobject.mk
          (Abelian.image.ι (kernel.ι (α.hom.app (op l)) ≫
            F.obj.map (homOfLE (Nat.le_trans (Nat.le_add_right m c) h)).op)) =
        Subobject.mk
          (Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫
            F.obj.map (homOfLE (Nat.le_add_right m c)).op)))
    (hS : ∀ m : ℕ, ∃ e : S.obj (op m) ≅
      Abelian.image (kernel.ι (α.hom.app (op (m + c))) ≫
        F.obj.map (homOfLE (Nat.le_add_right m c)).op),
      e.hom ≫ Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫
        F.obj.map (homOfLE (Nat.le_add_right m c)).op) = j.app (op m))
    (U : X.affineOpens) :
    let A := Γ(X, U.1)
    let R := AdicCompletion (I.ideal U) A
    let K := (I.ideal U).map (algebraMap A R)
    ∃ N : ModuleCat.{u} R, Module.Finite R N ∧
      ∃ L : Submodule R N,
        ∃ q : ∀ m : ℕ,
          ((ModuleCat.restrictScalars (algebraMap A R)).obj (ModuleCat.of R L))
            →ₗ[A] Γ(S.obj (op m), U.1),
          (∀ m : ℕ, Function.Surjective (q m)) ∧
          (∀ (a b : ℕ) (h : a ≤ b) (z : L),
            (S.map (homOfLE h).op).app U.1 (q b z) = q a z) ∧
          (∀ (m : ℕ) (z : L), q m z = 0 ↔
            L.subtype z ∈ K ^ (m + 1) • (⊤ : Submodule R N)) := by
  classical
  dsimp
  obtain ⟨N, P, f, hN, hP, p, r, hsurj, hpk, hrk, hf, ht⟩ :=
    coherentFormalModule_completed_projections_linear I F H α U
  let L := f.hom.ker
  have hp (a b : ℕ) (h : a ≤ b) (z : N) :
      (F.obj.map (homOfLE h).op).app U.1 (p b z) = p a z :=
    (ht b a h z).symm
  have hrange := coherentFormalModule_stabilized_kernel_section_range
    I F H α c hc U N P f hP p r hsurj hpk hrk hf ht
  let A := Γ(X, U.1)
  let R := AdicCompletion (I.ideal U) A
  let G := SheafOfModules.evaluation X.ringCatSheaf (op U.1)
  have hjmono (m : ℕ) : Mono (j.app (op m)) := by
    obtain ⟨e, he⟩ := hS m
    rw [← he]
    infer_instance
  have hi (m : ℕ) : Function.Injective (G.map (j.app (op m))) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  let t (m : ℕ) := (G.map (j.app (op m))).hom
  have hr (m : ℕ) : Set.range (fun z : L ↦ p m (L.subtype z)) = Set.range (t m) := by
    rw [hrange]
    obtain ⟨e, he⟩ := hS m
    apply Set.ext
    intro x
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨e.inv.app U.1 y, ?_⟩
      change (j.app (op m)).app U.1 (e.inv.app U.1 y) = _
      rw [← he]
      change (Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫
        F.obj.map (homOfLE (Nat.le_add_right m c)).op)).app U.1
          (e.hom.app U.1 (e.inv.app U.1 y)) = _
      have hh := congrArg (fun f ↦ f.app U.1 y) e.inv_hom_id
      change e.hom.app U.1 (e.inv.app U.1 y) = y at hh
      rw [hh]
    · rintro ⟨y, rfl⟩
      refine ⟨e.hom.app U.1 y, ?_⟩
      exact congrArg (fun f ↦ f.app U.1 y) he
  let e (m : ℕ) := LinearEquiv.ofInjective (t m) (hi m)
  let v (m : ℕ) :
      ((ModuleCat.restrictScalars (algebraMap A R)).obj (ModuleCat.of R L))
        →ₗ[A] Γ(F.obj.obj (op m), U.1) :=
    (p m).comp
      (((ModuleCat.restrictScalars (algebraMap A R)).map
        (ModuleCat.ofHom L.subtype)).hom)
  let q (m : ℕ) := (e m).symm.toLinearMap.comp
    ((v m).codRestrict (t m).range (fun z ↦ by
      exact (hr m).subset ⟨z, rfl⟩))
  have hjq (m : ℕ) (z : L) : t m (q m z) = p m (L.subtype z) := by
    have hh := (e m).apply_symm_apply
      (⟨v m z, (hr m).subset ⟨z, rfl⟩⟩ : (t m).range)
    exact congrArg Subtype.val hh
  refine ⟨N, hN, L, q, ?_, ?_, ?_⟩
  · intro m y
    obtain ⟨z, hz⟩ := (hr m).symm.subset ⟨y, rfl⟩
    refine ⟨z, hi m ?_⟩
    exact (hjq m z).trans hz
  · intro a b h z
    apply hi a
    change (j.app (op a)).app U.1
      ((S.map (homOfLE h).op).app U.1 (q b z)) = t a (q a z)
    have hn := congrArg (fun f ↦ f.app U.1 (q b z)) (j.naturality (homOfLE h).op)
    change (j.app (op a)).app U.1
        ((S.map (homOfLE h).op).app U.1 (q b z)) =
      (F.obj.map (homOfLE h).op).app U.1 (t b (q b z)) at hn
    rw [hn, hjq, hjq]
    exact hp a b h (L.subtype z)
  · intro m z
    have hz : q m z = 0 ↔ t m (q m z) = 0 := by
      constructor
      · intro h; rw [h, map_zero]
      · intro h; apply hi m; simpa using h
    exact hz.trans ((Iff.of_eq (congrArg (fun x ↦ x = 0) (hjq m z))).trans
      (hpk m (L.subtype z)))

end AlgebraicGeometry
