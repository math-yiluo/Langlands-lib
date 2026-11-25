/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorTensorStalkKernelSpan

/-!
# Local generators of an exterior tensor quotient kernel
-/

@[expose] public section

universe v
open CategoryTheory Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private theorem local_span_realization {X : Scheme.{v}} (M : X.Modules)
    (Q : ∀ V : X.Opens, Submodule (X.presheaf.obj (op V)) (M.val.obj (op V)))
    (hres : ∀ {U V : X.Opens} (h : V ≤ U) (t : M.val.obj (op U)),
      t ∈ Q U → M.presheaf.map (homOfLE h).op t ∈ Q V)
    (x : X) (m : M.presheaf.stalk x)
    (hm : m ∈ Submodule.span (X.presheaf.stalk x)
      {z | ∃ (V : X.Opens) (hxV : x ∈ V) (t : M.val.obj (op V)),
        t ∈ Q V ∧ M.presheaf.germ V x hxV t = z}) :
    ∃ (V : X.Opens) (hxV : x ∈ V) (t : M.val.obj (op V)),
      t ∈ Q V ∧ M.presheaf.germ V x hxV t = m := by
  induction hm using Submodule.span_induction with
  | mem z hz => exact hz
  | zero => exact ⟨⊤, by simp, 0, (Q ⊤).zero_mem, map_zero _⟩
  | add a b _ _ ha hb =>
    obtain ⟨U, hxU, a, ha, ea⟩ := ha
    obtain ⟨V, hxV, b, hb, eb⟩ := hb
    let W := U ⊓ V
    have hxW : x ∈ W := ⟨hxU, hxV⟩
    refine ⟨W, hxW, M.presheaf.map (homOfLE inf_le_left).op a +
      M.presheaf.map (homOfLE inf_le_right).op b,
      (Q W).add_mem (hres inf_le_left a ha) (hres inf_le_right b hb), ?_⟩
    rw [map_add, M.presheaf.germ_res_apply, M.presheaf.germ_res_apply, ea, eb]
  | smul c a _ ha =>
    obtain ⟨U, hxU, a, ha, ea⟩ := ha
    obtain ⟨V, hxV, c, ec⟩ := X.presheaf.exists_germ_eq c
    let W := U ⊓ V
    have hxW : x ∈ W := ⟨hxU, hxV⟩
    refine ⟨W, hxW, X.presheaf.map (homOfLE inf_le_right).op c •
      M.presheaf.map (homOfLE inf_le_left).op a,
      (Q W).smul_mem _ (hres inf_le_left a ha), ?_⟩
    rw [germ_smul, X.presheaf.germ_res_apply, M.presheaf.germ_res_apply, ec, ea]

set_option backward.isDefEq.respectTransparency false in
private theorem locally_mem_of_germ_mem_span {X : Scheme.{v}} (M : X.Modules)
    (Q : ∀ V : X.Opens, Submodule (X.presheaf.obj (op V)) (M.val.obj (op V)))
    (hres : ∀ {U V : X.Opens} (h : V ≤ U) (t : M.val.obj (op U)),
      t ∈ Q U → M.presheaf.map (homOfLE h).op t ∈ Q V)
    (U : X.Opens) (t : M.val.obj (op U)) (x : X) (hx : x ∈ U)
    (ht : M.presheaf.germ U x hx t ∈ Submodule.span (X.presheaf.stalk x)
      {z | ∃ (V : X.Opens) (hxV : x ∈ V) (a : M.val.obj (op V)),
        a ∈ Q V ∧ M.presheaf.germ V x hxV a = z}) :
    ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      M.presheaf.map (homOfLE hVU).op t ∈ Q V := by
  obtain ⟨V, hxV, a, ha, ea⟩ := local_span_realization M Q hres x _ ht
  obtain ⟨W, hxW, iV, iU, e⟩ := M.presheaf.germ_eq x hxV hx a t ea
  refine ⟨W, leOfHom iU, hxW, ?_⟩
  have h := hres (leOfHom iV) a ha
  have hV : homOfLE (leOfHom iV) = iV := Subsingleton.elim _ _
  have hU : homOfLE (leOfHom iU) = iU := Subsingleton.elim _ _
  rw [hU]
  rw [hV] at h
  exact e ▸ h

-- Elaborating both sheafification naturality equalities needs the larger local budget.
set_option backward.isDefEq.respectTransparency false in
private theorem relationSpan_map {X : Scheme.{v}} (S : ShortComplex X.Modules)
    (A : X.Modules) (r s : ℕ) {U V : X.Opens} (h : V ≤ U)
    (t : (exteriorPower A r ⊗ exteriorPower S.X₂ s).val.obj (op U))
    (ht : t ∈ exteriorTensorRelationSpan S A r s U) :
    (exteriorPower A r ⊗ exteriorPower S.X₂ s).val.map (homOfLE h).op t ∈
      exteriorTensorRelationSpan S A r s V := by
  induction ht using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, c, j, d, hj, rfl⟩ := hz
    apply Submodule.subset_span
    refine ⟨fun i ↦ A.val.map (homOfLE h).op (a i),
      fun i ↦ S.X₂.val.map (homOfLE h).op (c i), j,
      S.X₁.val.map (homOfLE h).op d, ?_, ?_⟩
    · dsimp only
      rw [hj]
      exact (PresheafOfModules.naturality_apply S.f.val (homOfLE h).op d).symm
    · change (exteriorPower A r ⊗ exteriorPower S.X₂ s).presheaf.map
        (homOfLE h).op _ = _
      rw [tmulSection_map]
      change tmulSection
        ((exteriorPower A r).val.map (homOfLE h).op (wedge (M := A) (r := r) (U := U) a))
        ((exteriorPower S.X₂ s).val.map (homOfLE h).op
          (wedge (M := S.X₂) (r := s) (U := U) c)) = _
      apply congrArg₂ (tmulSection (M := exteriorPower A r) (N := exteriorPower S.X₂ s))
      · exact wedge_map (homOfLE h) a
      · exact wedge_map (homOfLE h) c
  | zero => rw [map_zero]; exact (exteriorTensorRelationSpan S A r s V).zero_mem
  | add a b _ _ ha hb =>
    rw [map_add]
    exact (exteriorTensorRelationSpan S A r s V).add_mem ha hb
  | smul c a _ ha =>
    rw [PresheafOfModules.map_smul]
    exact (exteriorTensorRelationSpan S A r s V).smul_mem _ ha

set_option backward.isDefEq.respectTransparency false in
/-- A section killed by an exterior tensor quotient is locally a linear combination of
pure wedge tensors with an argument in the image of the first map. -/
theorem exteriorTensor_kernel_locally_mem_span {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (A : X.Modules) (r s : ℕ) (hs : s ≠ 0)
    (q : exteriorPower A r ⊗ exteriorPower S.X₂ s ⟶
      exteriorPower A r ⊗ exteriorPower S.X₃ s)
    (hq : ∀ (U : X.Opens) (a : Fin r → A.val.obj (op U))
      (c : Fin s → S.X₂.val.obj (op U)),
      q.val.app (op U)
        (tmulSection (wedge (M := A) (r := r) (U := U) a)
          (wedge (M := S.X₂) (r := s) (U := U) c)) =
        tmulSection (M := exteriorPower A r) (N := exteriorPower S.X₃ s)
          (wedge (M := A) (r := r) (U := U) a)
          (wedge (M := S.X₃) (r := s) (U := U) (fun i ↦ S.g.val.app (op U) (c i))))
    (U : X.Opens)
    (t : (exteriorPower A r ⊗ exteriorPower S.X₂ s).val.obj (op U))
    (ht : q.val.app (op U) t = 0) (x : X) (hx : x ∈ U) :
    ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      (exteriorPower A r ⊗ exteriorPower S.X₂ s).val.map (homOfLE hVU).op t ∈
        Submodule.span (X.presheaf.obj (op V))
          {z | ∃ (a : Fin r → A.val.obj (op V))
            (c : Fin s → S.X₂.val.obj (op V)) (j : Fin s)
            (d : S.X₁.val.obj (op V)), c j = S.f.val.app (op V) d ∧
              z = tmulSection (M := exteriorPower A r) (N := exteriorPower S.X₂ s)
                (wedge (M := A) (r := r) (U := V) a)
                (wedge (M := S.X₂) (r := s) (U := V) c)} := by
  let M := exteriorPower A r ⊗ exteriorPower S.X₂ s
  have hk : M.presheaf.germ U x hx t ∈ LinearMap.ker (q.stalkLinearMap x) := by
    rw [LinearMap.mem_ker, Hom.stalkLinearMap_germ]
    change (exteriorPower A r ⊗ exteriorPower S.X₃ s).presheaf.germ U x hx
      (q.val.app (op U) t) = 0
    rw [ht, map_zero]
  have hg := exteriorTensor_stalk_kernel_le_relationSpan S hS A r s hs q hq x hk
  exact locally_mem_of_germ_mem_span M (exteriorTensorRelationSpan S A r s)
    (fun h t ht ↦ relationSpan_map S A r s h t ht) U t x hx hg

end AlgebraicGeometry.Scheme.Modules
