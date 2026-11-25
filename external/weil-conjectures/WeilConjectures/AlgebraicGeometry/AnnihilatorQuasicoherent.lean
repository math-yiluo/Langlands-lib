/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion
import all WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent

/-! # Quasi-coherence of the annihilator subsheaf
Source: Stacks Project, Tag 01PO, proof of clause (1).
-/

@[expose] public section

universe u
open CategoryTheory TopologicalSpace Opposite
open scoped AlgebraicGeometry
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- A subsheaf with the affine-annihilator image is quasi-coherent for a finite-type ideal.
Source: Stacks Project, Tag 01PO, proof of (1).
(blueprint: lem-weil-pbc-annihilator-quasicoherent).

Proof: work on an affine open Spec A, writing F = M tilde and the ideal as I tilde.
Use the assumed image formula on every principal open. Put M' = {m : I m = 0}.
The inclusion (M')_f into M_f is injective by exactness of localization, and its
image is killed by I_f. Conversely write an element killed by I_f as m/f^n.
Choose finitely many generators g_i of I, using finite type on this affine open.
For every i, clear a power f^e_i in g_i m/f^n = 0. Choose e at least every e_i.
Then f^e m lies in M', and m/f^n = (f^e m)/f^(n+e) lies in (M')_f. For the
empty generator family use e = 0. These image identifications commute with
restriction and identify G on the principal-open basis with the tilde of M'.
Both maps into F are injective, so the identifications are unique and glue.
Thus G is locally a tilde sheaf and is quasi-coherent.
-/
theorem annihilator_subsheaf_quasicoherent (X : Scheme.{u}) (J : X.IdealSheafData)
    [J.toModules.IsFiniteType] (F : X.Modules) [F.IsQuasicoherent]
    (G : X.Modules) (ι : G ⟶ F) [Mono ι]
    (himage : ∀ (U : X.affineOpens) (s : Γ(F, U.1)),
      s ∈ Set.range (ι.app U.1) ↔ ∀ a ∈ J.ideal U, a • s = 0) :
    G.IsQuasicoherent := by
  classical
  have hinj (U : X.Opens) : Function.Injective (ι.app U) := by
    exact (ModuleCat.mono_iff_injective
      ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map ι)).mp
        (Functor.map_mono _ _)
  have hnat (V W : X.Opens) (h : V ≤ W) (s : Γ(G, W)) :
      ι.app V (G.presheaf.map (homOfLE h).op s) =
        F.presheaf.map (homOfLE h).op (ι.app W s) := by
    exact ConcreteCategory.congr_hom
      (ι.mapPresheaf.naturality (homOfLE h).op) s
  apply Scheme.Modules.isQuasicoherent_of_forall_isAffineOpen G
  · intro W hW f s
    obtain ⟨n, t, ht⟩ := Scheme.Modules.exists_map_eq_pow_smul_of_isAffineOpen F hW f
      (ι.app (X.basicOpen f) s)
    have : J.toModules.IsQuasicoherent := by
      have := SheafOfModules.isQuasicoherent_unit (R := J.subscheme.ringCatSheaf)
      have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
      have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf)
          ((SheafOfModules.pushforward J.subschemeι.toRingCatSheafHom).obj
            (SheafOfModules.unit J.subscheme.ringCatSheaf)) :=
        Scheme.Modules.isQuasicoherent_pushforward_of_isClosedImmersion J.subschemeι _
      exact Scheme.Modules.isQuasicoherent_kernel J.toPushforwardSubscheme
    have : (J.toModules.over W).IsFiniteType := Scheme.Modules.isFiniteType_over X J.toModules W
    have : Module.Finite Γ(X, W) Γ(J.toModules, W) :=
      (((Scheme.Modules.quasicoherent_finite_type_affine.{u, u} X).2 J.toModules inferInstance).1
        W hW).1.mp inferInstance
    obtain ⟨k, e, he⟩ := Module.Finite.exists_fin (R := Γ(X, W))
      (M := Γ(J.toModules, W))
    let g (j : Fin k) : Γ(X, W) := J.toModulesι.app W (e j)
    have hzero (j : Fin k) :
        F.presheaf.map (homOfLE (X.basicOpen_le f)).op
          (g j • t) = 0 := by
      rw [Scheme.Modules.map_smul, ht, smul_comm]
      have ha : X.presheaf.map (homOfLE (X.basicOpen_le f)).op
          (g j) ∈ J.ideal ⟨X.basicOpen f, hW.basicOpen f⟩ := by
        apply J.ideal_le_comap_ideal
          (U := ⟨X.basicOpen f, hW.basicOpen f⟩) (V := ⟨W, hW⟩) (X.basicOpen_le f)
        change g j ∈ (J.ideal ⟨W, hW⟩ : Set Γ(X, W))
        rw [← J.range_toModulesι_app ⟨W, hW⟩]
        exact ⟨e j, rfl⟩
      rw [(himage ⟨X.basicOpen f, hW.basicOpen f⟩ _).mp ⟨s, rfl⟩ _ ha, smul_zero]
    choose d hd using fun j ↦ Scheme.Modules.exists_pow_smul_eq_zero_of_isAffineOpen F hW f
      (g j • t) (hzero j)
    let D := Finset.univ.sup d
    have hgen (j : Fin k) : g j • (f ^ D • t) = 0 := by
      have hj : d j ≤ D := Finset.le_sup (Finset.mem_univ j)
      rw [smul_comm, ← Nat.sub_add_cancel hj, pow_add, mul_smul, hd j, smul_zero]
    have hann : ∀ a ∈ J.ideal ⟨W, hW⟩, a • (f ^ D • t) = 0 := by
      intro a ha
      change a ∈ (J.ideal ⟨W, hW⟩ : Set Γ(X, W)) at ha
      rw [← J.range_toModulesι_app ⟨W, hW⟩] at ha
      obtain ⟨z, rfl⟩ := ha
      let q : Γ(J.toModules, W) →ₗ[Γ(X, W)] Γ(F, W) :=
        (LinearMap.toSpanSingleton Γ(X, W) Γ(F, W) (f ^ D • t)).comp
          (J.toModulesι.val.app (op W)).hom
      have hspan : Submodule.span Γ(X, W) (Set.range e) ≤ q.ker := by
        apply Submodule.span_le.mpr
        rintro _ ⟨j, rfl⟩
        exact hgen j
      exact hspan (he ▸ Submodule.mem_top : z ∈ Submodule.span Γ(X, W) (Set.range e))
    obtain ⟨v, hv⟩ := (himage ⟨W, hW⟩ (f ^ D • t)).mpr hann
    refine ⟨D + n, v, hinj _ ?_⟩
    rw [hnat, hv, Scheme.Modules.map_smul, ht, Scheme.Modules.Hom.app_smul,
      map_pow, pow_add, mul_smul]
  · intro W hW f t ht
    have hz : F.presheaf.map (homOfLE (X.basicOpen_le f)).op (ι.app W t) = 0 := by
      rw [← hnat, ht, map_zero]
    obtain ⟨n, hn⟩ := Scheme.Modules.exists_pow_smul_eq_zero_of_isAffineOpen F hW f (ι.app W t) hz
    exact ⟨n, hinj W (by rw [Scheme.Modules.Hom.app_smul, hn, map_zero])⟩

end AlgebraicGeometry
