/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.RingTheory.AdicCompletion.Algebra
import all WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAffineKernelImageComparison
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.AdicKernelImageBound

/-! # Stabilized kernel section ranges
Source: Stacks Project, Lemma 087X, proof of claim (a).
(blueprint: lem-weil-pbc-stabilized-kernel-section-range). -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- The image of the true completed kernel equals the stabilized affine section range.

Source: Stacks Project, Lemma 087X, proof of claim (a), using Lemma 087W.
(blueprint: lem-weil-pbc-stabilized-kernel-section-range).

Proof: Put R equal to the completion and K equal to the extended ideal. R is
Noetherian. Artin--Rees applied to range(f) supplies a bound d. At l=max(m+c,m+d),
the image of f inverse(K^(l+1)N) modulo K^(m+1)M equals the image of ker(f).
The projection kernel criterion makes equality in this quotient exactly equality
under p_m. Surjectivity of p_l and hf and hqk identify the projected preimage
with the section range of the level-l categorical kernel followed by transition.
Quasi-coherence of the level kernels and affine exactness identify this with the
section range of its abelian image inclusion. Equality hc of subobjects identifies
this image with the image at m+c. Combining these equalities proves the assertion.
For the empty affine, the rings and modules are zero; zero and unit ideals also
satisfy the same calculation without requiring a nontriviality hypothesis. -/
theorem coherentFormalModule_stabilized_kernel_section_range
    {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F H : CoherentFormalModule X I) (α : F ⟶ H)
    (c : ℕ)
    (hc : ∀ (l m : ℕ) (h : m + c ≤ l),
      Subobject.mk
          (Abelian.image.ι (kernel.ι (α.hom.app (op l)) ≫
            F.obj.map (homOfLE (Nat.le_trans (Nat.le_add_right m c) h)).op)) =
        Subobject.mk
          (Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫
            F.obj.map (homOfLE (Nat.le_add_right m c)).op)))
    (U : X.affineOpens)
    (M N : ModuleCat.{u} (AdicCompletion (I.ideal U) Γ(X, U.1)))
    (f : M ⟶ N) (hN : Module.Finite (AdicCompletion (I.ideal U) Γ(X, U.1)) N)
    (p : ∀ n : ℕ,
      ((ModuleCat.restrictScalars
        (algebraMap Γ(X, U.1) (AdicCompletion (I.ideal U) Γ(X, U.1)))).obj M)
          →ₗ[Γ(X, U.1)] Γ(F.obj.obj (op n), U.1))
    (q : ∀ n : ℕ, N →+ Γ(H.obj.obj (op n), U.1))
    (hp : ∀ n : ℕ, Function.Surjective (p n))
    (hpk : ∀ (n : ℕ) (x : M), p n x = 0 ↔
      x ∈ ((I.ideal U).map
        (algebraMap Γ(X, U.1) (AdicCompletion (I.ideal U) Γ(X, U.1)))) ^ (n + 1) •
          (⊤ : Submodule (AdicCompletion (I.ideal U) Γ(X, U.1)) M))
    (hqk : ∀ (n : ℕ) (y : N), q n y = 0 ↔
      y ∈ ((I.ideal U).map
        (algebraMap Γ(X, U.1) (AdicCompletion (I.ideal U) Γ(X, U.1)))) ^ (n + 1) •
          (⊤ : Submodule (AdicCompletion (I.ideal U) Γ(X, U.1)) N))
    (hf : ∀ (n : ℕ) (x : M), q n (f x) = (α.hom.app (op n)).app U.1 (p n x))
    (ht : ∀ (l m : ℕ) (h : m ≤ l) (x : M),
      p m x = (F.obj.map (homOfLE h).op).app U.1 (p l x)) :
    ∀ m : ℕ, Set.range (fun z : f.hom.ker ↦ p m (f.hom.ker.subtype z)) =
      Set.range ((Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫
        F.obj.map (homOfLE (Nat.le_add_right m c)).op)).app U.1) := by
  classical
  let R := AdicCompletion (I.ideal U) Γ(X, U.1)
  let K := (I.ideal U).map (algebraMap Γ(X, U.1) R)
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have : IsNoetherianRing R := AdicCompletion.isNoetherianRing (I.ideal U)
  obtain ⟨d, hd⟩ := LinearMap.adic_kernel_image_bound K f.hom
  intro m
  let l := max (m + c) (m + d)
  have hl : m + c ≤ l := le_max_left _ _
  have hld : m + d ≤ l := le_max_right _ _
  have hml : m ≤ l := Nat.le_trans (Nat.le_add_right m c) hl
  have heq := (quotient_map_eq_iff_additive_image_eq
    (K ^ (m + 1) • (⊤ : Submodule R M))
    ((K ^ (l + 1) • (⊤ : Submodule R N)).comap f.hom)
    f.hom.ker (p m).toAddMonoidHom (hpk m)).mp (hd l m hld)
  have htrans := kernel_transition_range I F H α U K M N f
    (fun n ↦ (p n).toAddMonoidHom) q hp hqk hf ht l m hml
  have qc (n : ℕ) : (F.obj.obj (op n)).IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp
      (F.property.1 n)).1
  have qh (n : ℕ) : (H.obj.obj (op n)).IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp
      (H.property.1 n)).1
  have := qc l
  have := qh l
  have := qc m
  have := Scheme.Modules.isQuasicoherent_kernel (α.hom.app (op l))
  let a := kernel.ι (α.hom.app (op l)) ≫ F.obj.map (homOfLE hml).op
  let b := kernel.ι (α.hom.app (op (m + c))) ≫
    F.obj.map (homOfLE (Nat.le_add_right m c)).op
  have him := (Scheme.Modules.quasiCoherent_cokernel_image a).2.2.2.2.2.2.2.2 U
  have hs : Subobject.mk (Abelian.image.ι a) = Subobject.mk (Abelian.image.ι b) :=
    hc l m hl
  let e := Subobject.isoOfMkEqMk (Abelian.image.ι a) (Abelian.image.ι b) hs
  have hr : Set.range ((Abelian.image.ι a).app U.1) =
      Set.range ((Abelian.image.ι b).app U.1) := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨e.hom.app U.1 z, ?_⟩
      have hw : e.hom ≫ Abelian.image.ι b = Abelian.image.ι a := by simp [e]
      exact congrArg (fun t ↦ t.app U.1 z) hw
    · rintro ⟨z, rfl⟩
      refine ⟨e.inv.app U.1 z, ?_⟩
      have hw : e.inv ≫ Abelian.image.ι a = Abelian.image.ι b := by simp [e]
      exact congrArg (fun t ↦ t.app U.1 z) hw
  have hk : Set.image (fun x : M ↦ p m x) (f.hom.ker : Set M) =
      Set.range (fun z : f.hom.ker ↦ p m (f.hom.ker.subtype z)) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z.val, z.property, rfl⟩
  have hh : Set.image (fun x : M ↦ p m x) (f.hom.ker : Set M) =
      Set.range (a.app U.1) := heq.symm.trans htrans
  exact hk.symm.trans (hh.trans (him.1.symm.trans hr))

end AlgebraicGeometry
