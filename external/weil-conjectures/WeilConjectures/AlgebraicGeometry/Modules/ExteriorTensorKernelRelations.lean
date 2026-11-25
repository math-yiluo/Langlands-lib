/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorTensorKernelLocallySpanned
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorTensorLiftHomExt

/-!
# A generator criterion for annihilating an exterior quotient kernel
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- The zeroth exterior power is the structure sheaf, by an isomorphism sending the empty wedge
over every open to `1`. Sectionwise, the empty wedge generates `⋀⁰ M(U)` freely over `𝒪_X(U)`
(`exteriorPower.zeroEquiv`); these identifications commute with restriction and sheafify. -/
theorem exists_exteriorPower_zero_iso_wedge {X : Scheme.{v}} (M : X.Modules) :
    ∃ e : M.exteriorPower 0 ≅ SheafOfModules.unit X.ringCatSheaf,
      ∀ U : X.Opens, e.hom.val.app (op U) (wedge (M := M) (r := 0) (U := U) Fin.elim0) =
        (1 : X.presheaf.obj (op U)) := by
  let P := _root_.PresheafOfModules.exteriorPower (R := X.presheaf) M.val 0
  let e₀ : P ≅ (SheafOfModules.unit X.ringCatSheaf).val :=
    PresheafOfModules.isoMk
      (fun U ↦ (_root_.exteriorPower.zeroEquiv (X.presheaf.obj U) (M.val.obj U)).toModuleIso)
      (by
        intro U V f
        apply ModuleCat.hom_ext
        apply _root_.exteriorPower.linearMap_ext (R := X.presheaf.obj U)
        apply AlternatingMap.ext
        intro a
        change _root_.exteriorPower.zeroEquiv (X.presheaf.obj V) (M.val.obj V)
            (P.map f (_root_.exteriorPower.ιMulti (X.presheaf.obj U) 0 a)) =
          X.presheaf.map f
            (_root_.exteriorPower.zeroEquiv (X.presheaf.obj U) (M.val.obj U)
              (_root_.exteriorPower.ιMulti (X.presheaf.obj U) 0 a))
        exact (congrArg (_root_.exteriorPower.zeroEquiv (X.presheaf.obj V) (M.val.obj V))
          (_root_.PresheafOfModules.exteriorPower_map_ιMulti (R := X.presheaf) M.val 0 f a)).trans
          ((_root_.exteriorPower.zeroEquiv_ιMulti _).trans
            ((congrArg (fun x ↦ X.presheaf.map f x)
              (_root_.exteriorPower.zeroEquiv_ιMulti a)).trans
              (X.presheaf.map f).hom.map_one).symm))
  let adj := PresheafOfModules.sheafificationAdjunction.{v} (𝟙 X.ringCatSheaf.obj)
  let e : M.exteriorPower 0 ≅ SheafOfModules.unit X.ringCatSheaf :=
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso e₀ ≪≫
      asIso (C := SheafOfModules.{v} X.ringCatSheaf)
        (adj.counit.app (SheafOfModules.unit X.ringCatSheaf))
  have he : adj.homEquiv _ _ e.hom = e₀.hom := by
    apply (adj.homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply, adj.homEquiv_counit]
    rfl
  refine ⟨e, fun U ↦ ?_⟩
  have h := congrArg
    (fun k ↦ k.app (op U) (_root_.exteriorPower.ιMulti (X.presheaf.obj (op U)) 0
      (M := M.val.obj (op U)) Fin.elim0)) he
  change e.hom.val.app (op U) (wedge (M := M) (r := 0) (U := U) Fin.elim0) =
    _root_.exteriorPower.zeroEquiv (X.presheaf.obj (op U)) (M.val.obj (op U))
      (_root_.exteriorPower.ιMulti (X.presheaf.obj (op U)) 0 Fin.elim0) at h
  exact h.trans (_root_.exteriorPower.zeroEquiv_ιMulti
    (R := X.presheaf.obj (op U)) (M := M.val.obj (op U)) _)

set_option backward.isDefEq.respectTransparency false in
private theorem exteriorTensor_zero_mono {X : Scheme.{v}}
    (A B C : X.Modules) (r : ℕ) (g : B ⟶ C)
    (q : exteriorPower A r ⊗ exteriorPower B 0 ⟶
      exteriorPower A r ⊗ exteriorPower C 0)
    (hq : ∀ (U : X.Opens) (a : Fin r → A.val.obj (op U))
      (c : Fin 0 → B.val.obj (op U)),
      q.val.app (op U)
        (tmulSection (wedge (M := A) (r := r) (U := U) a)
          (wedge (M := B) (r := 0) (U := U) c)) =
        tmulSection (M := exteriorPower A r) (N := exteriorPower C 0)
          (wedge (M := A) (r := r) (U := U) a)
          (wedge (M := C) (r := 0) (U := U) (fun i ↦ g.val.app (op U) (c i)))) :
    Mono q := by
  obtain ⟨eB, hB⟩ := exists_exteriorPower_zero_iso_wedge B
  obtain ⟨eC, hC⟩ := exists_exteriorPower_zero_iso_wedge C
  let e := eB ≪≫ eC.symm
  have he (U : X.Opens) (c : Fin 0 → B.val.obj (op U)) :
      e.hom.val.app (op U) (wedge (M := B) (r := 0) (U := U) c) =
        wedge (M := C) (r := 0) (U := U) Fin.elim0 := by
    have hc : c = Fin.elim0 := Subsingleton.elim _ _
    subst c
    change eC.inv.val.app (op U)
      (eB.hom.val.app (op U) (wedge (M := B) (r := 0) (U := U) Fin.elim0)) = _
    rw [hB U, ← hC U]
    exact congrArg
      (fun f ↦ f.val.app (op U) (wedge (M := C) (r := 0) (U := U) Fin.elim0))
      eC.hom_inv_id
  have hqe : q = (Iso.refl (exteriorPower A r) ⊗ᵢ e).hom := by
    apply exteriorTensor_lift_hom_ext (𝟙 B) r 0
    intro U a c
    rw [hq]
    have hc : (fun i ↦ g.val.app (op U) ((𝟙 B : B ⟶ B).val.app (op U) (c i))) =
        (Fin.elim0 : Fin 0 → C.val.obj (op U)) := Subsingleton.elim _ _
    rw [hc]
    change _ = ((𝟙 (exteriorPower A r)) ⊗ₘ e.hom).app U _
    rw [tensorHom_app_tmulSection]
    change _ = tmulSection (M := exteriorPower A r) (N := exteriorPower C 0)
      (wedge (M := A) (r := r) (U := U) a) (e.hom.val.app (op U) _)
    rw [he]
  rw [hqe]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- A morphism kills the exterior quotient kernel if it kills the quotient relations. -/
theorem exteriorTensor_kernel_eq_zero_of_relations {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (A D : X.Modules) (r s : ℕ)
    (q : exteriorPower A r ⊗ exteriorPower S.X₂ s ⟶
      exteriorPower A r ⊗ exteriorPower S.X₃ s)
    (ψ : exteriorPower A r ⊗ exteriorPower S.X₂ s ⟶ D)
    (hq : ∀ (U : X.Opens) (a : Fin r → A.val.obj (op U))
      (c : Fin s → S.X₂.val.obj (op U)),
      q.val.app (op U)
        (tmulSection (wedge (M := A) (r := r) (U := U) a)
          (wedge (M := S.X₂) (r := s) (U := U) c)) =
        tmulSection (M := exteriorPower A r) (N := exteriorPower S.X₃ s)
          (wedge (M := A) (r := r) (U := U) a)
          (wedge (M := S.X₃) (r := s) (U := U) (fun i ↦ S.g.val.app (op U) (c i))))
    (hzero : ∀ (U : X.Opens) (a : Fin r → A.val.obj (op U))
      (c : Fin s → S.X₂.val.obj (op U)) (j : Fin s) (d : S.X₁.val.obj (op U)),
      c j = S.f.val.app (op U) d →
      ψ.val.app (op U)
        (tmulSection (wedge (M := A) (r := r) (U := U) a)
          (wedge (M := S.X₂) (r := s) (U := U) c)) = 0) :
    kernel.ι q ≫ ψ = 0 := by
  by_cases hs : s = 0
  · subst s
    have : Mono q := exteriorTensor_zero_mono A S.X₂ S.X₃ r S.g q hq
    have hι : kernel.ι q = 0 := (cancel_mono q).mp (by simp)
    rw [hι, zero_comp]
  ext U k
  change ψ.val.app (op U) ((kernel.ι q).val.app (op U) k) = 0
  let t := (kernel.ι q).val.app (op U) k
  have ht : q.val.app (op U) t = 0 := by
    have h := congrArg
      (fun f ↦ f.val.app (op U) k) (kernel.condition q)
    exact h
  apply D.isSheaf.section_ext
  intro x hx
  obtain ⟨V, hVU, hxV, hspan⟩ :=
    exteriorTensor_kernel_locally_mem_span S hS A r s hs q hq U t ht x hx
  refine ⟨V, hVU, hxV, ?_⟩
  have hle : Submodule.span (X.presheaf.obj (op V))
      {z | ∃ (a : Fin r → A.val.obj (op V))
        (c : Fin s → S.X₂.val.obj (op V)) (j : Fin s)
        (d : S.X₁.val.obj (op V)), c j = S.f.val.app (op V) d ∧
          z = tmulSection (M := exteriorPower A r) (N := exteriorPower S.X₂ s)
            (wedge (M := A) (r := r) (U := V) a) (wedge (M := S.X₂) (r := s) (U := V) c)} ≤
      LinearMap.ker (ψ.val.app (op V)).hom := by
    apply Submodule.span_le.mpr
    rintro z ⟨a, c, j, d, hcd, rfl⟩
    exact hzero V a c j d hcd
  have hz := hle hspan
  change ψ.val.app (op V)
    ((exteriorPower A r ⊗ exteriorPower S.X₂ s).val.map (homOfLE hVU).op t) = 0 at hz
  change D.presheaf.map (homOfLE hVU).op (ψ.val.app (op U) t) =
    D.presheaf.map (homOfLE hVU).op 0
  have hn := PresheafOfModules.naturality_apply ψ.val (homOfLE hVU).op t
  exact hn.symm.trans (hz.trans (map_zero (D.val.map (homOfLE hVU).op).hom).symm)

end AlgebraicGeometry.Scheme.Modules
