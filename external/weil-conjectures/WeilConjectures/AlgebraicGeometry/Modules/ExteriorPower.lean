/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.LinearAlgebra.ExteriorPower.Top
public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
public import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.ExteriorPower

/-!
# Exterior powers of sheaves of modules on a scheme

For a sheaf of `𝒪_X`-modules `M` and `r: ℕ`, the exterior power `⋀ʳ M` is the sheafification
of the presheaf of modules `U ↦ ⋀ʳ_{𝒪(U)} M(U)` (`PresheafOfModules.exteriorPower`).

## Main declarations

- `AlgebraicGeometry.Scheme.Modules.exteriorPower M r`: the exterior power `⋀ʳ M`.
- `AlgebraicGeometry.Scheme.Modules.wedge`: the section `m₁ ∧ ⋯ ∧ m_r` of `⋀ʳ M` over `U` of
  sections `mᵢ` of `M` over `U`.
- `AlgebraicGeometry.Scheme.Modules.isFreeGenerator_wedge`: if `M` is locally free on `U` with
  basis `m₁, …, m_r` (on a basis of the topology of `U`), then `m₁ ∧ ⋯ ∧ m_r` is a free generator
  of `⋀ʳ M` on `U`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

section Sheafification

variable (P : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj)

local instance {U V : X.Opens} (i : V ⟶ U) :
    Module Γ(X, V)
      ((ModuleCat.restrictScalars (X.ringCatSheaf.obj.map i.op).hom).obj (P.obj (op V))) :=
  inferInstanceAs (Module Γ(X, V) (P.obj (op V)))

/-- The sheafification of a presheaf of modules on a scheme. -/
noncomputable abbrev sheafificationObj : X.Modules :=
  (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P

/-- The canonical morphism from a presheaf of modules to (the underlying presheaf of) its
sheafification. -/
noncomputable def toSheafificationObj :=
  (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P

lemma toSheafificationObj_app_smul {U : X.Opens} (a : Γ(X, U)) (e : P.obj (op U)) :
    (toSheafificationObj P).app (op U) (a • e) = a • (toSheafificationObj P).app (op U) e :=
  ((toSheafificationObj P).app (op U)).hom.map_smul a e

lemma toSheafificationObj_app_map {U V : X.Opens} (i : V ⟶ U) (e : P.obj (op U)) :
    (toSheafificationObj P).app (op V) (P.map i.op e) =
      (sheafificationObj P).presheaf.map i.op ((toSheafificationObj P).app (op U) e) :=
  _root_.PresheafOfModules.naturality_apply (toSheafificationObj P) i.op e

lemma equalizerSieve_mem_of_toSheafificationObj_app_eq {U : X.Opens} (e e' : P.obj (op U))
    (h : (toSheafificationObj P).app (op U) e = (toSheafificationObj P).app (op U) e') :
    Presheaf.equalizerSieve (F := P.presheaf) (X := op U) e e' ∈
      Opens.grothendieckTopology X U :=
  Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X)
    (toSheafify (Opens.grothendieckTopology X) P.presheaf) e e' h

lemma imageSieve_mem_toSheafificationObj {U : X.Opens} (q : Γ(sheafificationObj P, U)) :
    Presheaf.imageSieve (toSheafify (Opens.grothendieckTopology X) P.presheaf) q ∈
      Opens.grothendieckTopology X U :=
  Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
    (toSheafify (Opens.grothendieckTopology X) P.presheaf) (U := op U) q
/-- Restricting `a • e|_V` to `W ⊆ V` gives `a|_W • e|_W`. -/
lemma presheafOfModules_map_smul_map {U V W : X.Opens} (i : W ⟶ V) (j : V ⟶ U) (k : W ⟶ U)
    (a : Γ(X, V)) (e : P.obj (op U)) :
    P.map i.op (a • P.map j.op e) = X.presheaf.map i.op a • P.map k.op e := by
  rw [Subsingleton.elim k (i ≫ j), _root_.PresheafOfModules.map_smul, op_comp,
    P.map_comp_apply]
  rfl

/-- **Free generators of a sheafification.** Let `e` be a section over `U` of a presheaf of
modules `P` which is a free generator of `P` locally on `U`: every point of an open `V ⊆ U` has an
open neighbourhood `W ⊆ V` on which `a ↦ a • e|_W` is bijective. Then the image of `e` in the
sheafification of `P` is a free generator over `U`. -/
lemma isFreeGenerator_toSheafificationObj_app {U : X.Opens} (e : P.obj (op U))
    (he : ∀ (V : X.Opens) (hV : V ≤ U), ∀ x ∈ V, ∃ (W : X.Opens) (hW : W ≤ V), x ∈ W ∧
      Function.Bijective fun a : Γ(X, W) ↦ a • P.map (homOfLE (hW.trans hV)).op e) :
    IsFreeGenerator (M := sheafificationObj P) ((toSheafificationObj P).app (op U) e) := by
  refine isFreeGenerator_of_locally _ (fun V hV a b hab ↦ ?_) (fun V hV q ↦ ?_)
  · dsimp only at hab
    rw [← toSheafificationObj_app_map, ← toSheafificationObj_app_smul,
      ← toSheafificationObj_app_smul] at hab
    have hS := equalizerSieve_mem_of_toSheafificationObj_app_eq P _ _ hab
    refine X.ext_of_mem (S := Presheaf.equalizerSieve (F := X.presheaf) (X := op V) a b)
      (fun x hx ↦ ?_) fun _ _ h ↦ h
    obtain ⟨W', f', hf', hxW'⟩ := hS x hx
    obtain ⟨W, hW, hxW, hbij⟩ := he W' ((leOfHom f').trans hV) x hxW'
    refine ⟨W, homOfLE hW ≫ f', hbij.1 ?_, hxW⟩
    have h2 : P.map (homOfLE hW ≫ f').op (a • P.map (homOfLE hV).op e) =
        P.map (homOfLE hW ≫ f').op (b • P.map (homOfLE hV).op e) := by
      rw [op_comp, P.map_comp_apply, P.map_comp_apply]
      exact congrArg (P.map (homOfLE hW).op) hf'
    rw [presheafOfModules_map_smul_map P _ _ (homOfLE (hW.trans ((leOfHom f').trans hV))),
      presheafOfModules_map_smul_map P _ _ (homOfLE (hW.trans ((leOfHom f').trans hV)))] at h2
    exact h2
  · let σ := (toSheafificationObj P).app (op U) e
    let S : Sieve V :=
      { arrows W i := ∃ a : Γ(X, W), (sheafificationObj P).presheaf.map i.op q =
          a • (sheafificationObj P).presheaf.map (homOfLE ((leOfHom i).trans hV)).op σ
        downward_closed {W W₁} i hi g := by
          obtain ⟨a, ha⟩ := hi
          refine ⟨X.presheaf.map g.op a, ?_⟩
          rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ha, map_smul,
            presheaf_map_map_apply]
          rfl }
    refine ⟨S, fun x hx ↦ ?_, fun W i hi ↦ hi⟩
    obtain ⟨W₁, f₁, ⟨t, ht⟩, hxW₁⟩ := imageSieve_mem_toSheafificationObj P q x hx
    obtain ⟨W, hW, hxW, hbij⟩ := he W₁ ((leOfHom f₁).trans hV) x hxW₁
    obtain ⟨a, ha⟩ := hbij.2 (P.map (homOfLE hW).op t)
    refine ⟨W, homOfLE hW ≫ f₁, ⟨a, ?_⟩, hxW⟩
    have ht' : (toSheafificationObj P).app (op W₁) t =
        (sheafificationObj P).presheaf.map f₁.op q := ht
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ← ht',
      ← toSheafificationObj_app_map, ← ha]
    dsimp only
    rw [toSheafificationObj_app_smul, toSheafificationObj_app_map]

end Sheafification
section ExteriorPower

variable (M : X.Modules) (r : ℕ)

/-- **The exterior power `⋀ʳ M` of a sheaf of modules**: the sheafification of the presheaf of
modules `U ↦ ⋀ʳ_{𝒪(U)} M(U)`. -/
noncomputable def exteriorPower : X.Modules :=
  sheafificationObj (_root_.PresheafOfModules.exteriorPower (R := X.presheaf) M.val r)

variable {M r}

/-- The section `v₁ ∧ ⋯ ∧ v_r` of `⋀ʳ M` over `U`, for sections `vᵢ` of `M` over `U`. -/
noncomputable def wedge {U : X.Opens} (v : Fin r → Γ(M, U)) : Γ(M.exteriorPower r, U) :=
  (toSheafificationObj _).app (op U) (_root_.exteriorPower.ιMulti _ r v)
/-- Restricting `v₁ ∧ ⋯ ∧ v_r` gives the wedge product of the restrictions. -/
lemma wedge_map {U V : X.Opens} (i : V ⟶ U) (v : Fin r → Γ(M, U)) :
    (M.exteriorPower r).presheaf.map i.op (wedge v) =
      wedge fun k ↦ M.presheaf.map i.op (v k) := by
  rw [wedge]
  erw [← toSheafificationObj_app_map, PresheafOfModules.exteriorPower_map_ιMulti]
  rfl

/-- **A local basis gives a free generator of the top exterior power.** If `v₁, …, v_r` are
sections of `M` over `U` which restrict to a basis of the sections of `M` over the opens `W` of
a basis of the topology of `U`, then `v₁ ∧ ⋯ ∧ v_r` is a free generator of `⋀ʳ M` over `U`. -/
theorem isFreeGenerator_wedge {U : X.Opens} (v : Fin r → Γ(M, U))
    (hv : ∀ (V : X.Opens) (hV : V ≤ U), ∀ x ∈ V, ∃ (W : X.Opens) (hW : W ≤ V), x ∈ W ∧
      ∃ b : Module.Basis (Fin r) Γ(X, W) Γ(M, W),
        ∀ k, b k = M.presheaf.map (homOfLE (hW.trans hV)).op (v k)) :
    IsFreeGenerator (wedge v) := by
  refine isFreeGenerator_toSheafificationObj_app _ _ fun V hV x hx ↦ ?_
  obtain ⟨W, hW, hxW, b, hb⟩ := hv V hV x hx
  refine ⟨W, hW, hxW, ?_⟩
  erw [PresheafOfModules.exteriorPower_map_ιMulti]
  have h : (fun k ↦ M.val.restrictₛₗ (homOfLE (hW.trans hV)).op (v k)) = ⇑b :=
    funext fun k ↦ (hb k).symm
  rw [h]
  exact _root_.exteriorPower.bijective_smul_ιMulti_basis b

end ExteriorPower

end AlgebraicGeometry.Scheme.Modules
