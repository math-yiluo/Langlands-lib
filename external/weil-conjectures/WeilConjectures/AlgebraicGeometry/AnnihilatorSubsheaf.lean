/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Construction of the annihilator subsheaf

Source: Stacks Project, Tag 01PO, first sentence of the proof.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

noncomputable section

private def annihilatorSections (X : Scheme.{u}) (J : X.IdealSheafData)
    (F : X.Modules) (U : X.Opens) : Submodule Γ(X, U) Γ(F, U) where
  carrier := {s | ∀ (V : X.Opens) (h : V ≤ U), ∀ a ∈ J.idealOfOpens V,
    a • F.presheaf.map (homOfLE h).op s = 0}
  zero_mem' := by simp
  add_mem' := by
    intro s t hs ht V h a ha
    simp only [map_add, smul_add, hs V h a ha, ht V h a ha, add_zero]
  smul_mem' := by
    intro r s hs V h a ha
    rw [F.map_smul, smul_comm, hs V h a ha, smul_zero]

private def annihilatorPresheaf (X : Scheme.{u}) (J : X.IdealSheafData)
    (F : X.Modules) : F.val.Submodule where
  obj U := annihilatorSections X J F U.unop
  map {U V} f := by
    intro s hs
    change ∀ (W : X.Opens) (h : W ≤ V.unop), ∀ a ∈ J.idealOfOpens W,
      a • F.presheaf.map (homOfLE h).op (F.presheaf.map f s) = 0
    intro W h a ha
    have hh := hs W (h.trans f.unop.le) a ha
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    convert hh using 1

private theorem ideal_restrict_mem (X : Scheme.{u}) (J : X.IdealSheafData)
    {U V : X.Opens} (h : V ≤ U) {a : Γ(X, U)} (ha : a ∈ J.idealOfOpens U) :
    X.presheaf.map (homOfLE h).op a ∈ J.idealOfOpens V := by
  change a ∈ (J.idealOfOpens U : Set Γ(X, U)) at ha
  change X.presheaf.map (homOfLE h).op a ∈ (J.idealOfOpens V : Set Γ(X, V))
  rw [← J.range_toModulesι_app_eq_idealOfOpens] at ha ⊢
  obtain ⟨b, rfl⟩ := ha
  refine ⟨J.toModules.presheaf.map (homOfLE h).op b, ?_⟩
  exact ConcreteCategory.congr_hom (J.toModulesι.mapPresheaf.naturality (homOfLE h).op) b

private theorem annihilatorPresheaf_isSheaf (X : Scheme.{u}) (J : X.IdealSheafData)
    (F : X.Modules) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (annihilatorPresheaf X J F).toPresheafOfModules.presheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr
  intro I U sf hsf
  let A : TopCat.Sheaf Ab X := ⟨F.presheaf, F.isSheaf⟩
  have hcompat : TopCat.Presheaf.IsCompatible F.presheaf U (fun i ↦ (sf i).val) := by
    intro i j
    exact congrArg Subtype.val (hsf i j)
  obtain ⟨s, hs, huniq⟩ := A.existsUnique_gluing U (fun i ↦ (sf i).val) hcompat
  change ∀ i, F.presheaf.map (Opens.leSupr U i).op s = (sf i).val at hs
  have hmem : s ∈ annihilatorSections X J F (iSup U) := by
    intro V hV a ha
    apply A.eq_of_locally_eq' (fun i ↦ V ⊓ U i) V
      (fun i ↦ homOfLE inf_le_left) (by
        intro x hx
        obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hV hx)
        exact Opens.mem_iSup.mpr ⟨i, hx, hi⟩) _ 0
    intro i
    rw [map_zero, F.map_smul]
    have hh := (sf i).property (V ⊓ U i) inf_le_right
      (X.presheaf.map (homOfLE inf_le_left).op a) (ideal_restrict_mem X J _ ha)
    have heq : F.presheaf.map (homOfLE inf_le_left : V ⊓ U i ⟶ V).op
        (F.presheaf.map (homOfLE hV).op s) =
        F.presheaf.map (homOfLE inf_le_right : V ⊓ U i ⟶ U i).op (sf i).val := by
      rw [← hs i]
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    rw [heq]
    exact hh
  refine ⟨⟨s, hmem⟩, ?_, ?_⟩
  · intro i
    apply Subtype.ext
    exact hs i
  · intro t ht
    apply Subtype.ext
    apply huniq t.val
    intro i
    exact congrArg Subtype.val (ht i)

/-- The local annihilation condition defines a subsheaf, without any finiteness
or quasi-coherence hypothesis.
Source: Stacks Project, Tag 01PO, proof, first sentence.
(blueprint: lem-weil-pbc-annihilator-subsheaf-construction).

Proof: local annihilation is closed under addition and scalar multiplication and
under restriction, giving a submodule presheaf. Glue a compatible family in F.
For a local ideal section on V, restrict its product with the glued section to
V intersected with every member of the cover. Each restricted product is zero by
local annihilation of that member. Separatedness of F makes the product zero on V.
Uniqueness follows from uniqueness in F. The inclusion is sectionwise the subtype
inclusion, hence a monomorphism, and its image is precisely the defining condition.
-/
theorem exists_annihilator_subsheaf (X : Scheme.{u}) (J : X.IdealSheafData)
    (F : X.Modules) :
    ∃ (G : X.Modules) (ι : G ⟶ F), Mono ι ∧
      ∀ (U : X.Opens) (s : Γ(F, U)),
        s ∈ Set.range (ι.app U) ↔
          ∀ (V : X.Opens) (h : V ≤ U), ∀ a ∈ J.idealOfOpens V,
            a • F.presheaf.map (homOfLE h).op s = 0 := by
  let N := annihilatorPresheaf X J F
  let G : X.Modules := ⟨N.toPresheafOfModules, annihilatorPresheaf_isSheaf X J F⟩
  let ι : G ⟶ F := ⟨N.ι⟩
  have hmono : Mono ι :=
    (Scheme.Modules.toPresheafOfModules X).mono_of_mono_map (by
      change Mono N.ι
      infer_instance)
  refine ⟨G, ι, hmono, ?_⟩
  intro U s
  change (∃ t : annihilatorSections X J F U, t.val = s) ↔
    s ∈ annihilatorSections X J F U
  exact ⟨fun ⟨t, ht⟩ ↦ ht ▸ t.property, fun hs ↦ ⟨⟨s, hs⟩, rfl⟩⟩

end
end AlgebraicGeometry
