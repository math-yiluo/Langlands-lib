/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import WeilConjectures.AlgebraicGeometry.AnnihilatorQuasicoherent
import all WeilConjectures.AlgebraicGeometry.CoherentSupportVanishingIdealNilpotence
import all WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine

/-! # The canonical annihilator of an ideal power

Source: Stacks Project, Properties, Tags 01PO and 01PQ.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme

/-- Sections locally annihilated by a module inclusion into the structure sheaf. 
(blueprint: lem-weil-pbc-ideal-power-annihilator-quasicoherent)
-/
def idealAnnihilatorSections {X : Scheme.{u}} {P : X.Modules}
    (j : P ⟶ SheafOfModules.unit X.ringCatSheaf) (F : X.Modules)
    (W : X.Opens) : Submodule Γ(X, W) Γ(F, W) where
  carrier := {s | ∀ (V : X.Opens) (h : V ≤ W) (b : Γ(P, V)),
    (show Γ(X, V) from j.app V b) • F.presheaf.map (homOfLE h).op s = 0}
  zero_mem' := by simp
  add_mem' := by
    intro s t hs ht V h b
    simp only [map_add, smul_add, hs V h b, ht V h b, add_zero]
  smul_mem' := by
    intro r s hs V h b
    rw [F.map_smul, smul_comm, hs V h b, smul_zero]

/-- The local annihilation condition is stable under restriction. 
(blueprint: lem-weil-pbc-ideal-power-annihilator-quasicoherent)
-/
def idealAnnihilatorPresheaf {X : Scheme.{u}} {P : X.Modules}
    (j : P ⟶ SheafOfModules.unit X.ringCatSheaf) (F : X.Modules) : F.val.Submodule where
  obj W := idealAnnihilatorSections j F W.unop
  map {W V} f := by
    intro s hs
    change ∀ (T : X.Opens) (h : T ≤ V.unop) (b : Γ(P, T)),
      (show Γ(X, T) from j.app T b) •
        F.presheaf.map (homOfLE h).op (F.presheaf.map f s) = 0
    intro T h b
    have hh := hs T (h.trans f.unop.le) b
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    convert hh using 1

/-- (blueprint: lem-weil-pbc-ideal-power-annihilator-quasicoherent) -/
theorem idealAnnihilatorPresheaf_isSheaf {X : Scheme.{u}} {P : X.Modules}
    (j : P ⟶ SheafOfModules.unit X.ringCatSheaf) (F : X.Modules) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (idealAnnihilatorPresheaf j F).toPresheafOfModules.presheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr
  intro T W sf hsf
  let A : TopCat.Sheaf Ab X := ⟨F.presheaf, F.isSheaf⟩
  have hcompat : TopCat.Presheaf.IsCompatible F.presheaf W (fun i ↦ (sf i).val) := by
    intro i k
    exact congrArg Subtype.val (hsf i k)
  obtain ⟨s, hs, huniq⟩ := A.existsUnique_gluing W (fun i ↦ (sf i).val) hcompat
  change ∀ i, F.presheaf.map (Opens.leSupr W i).op s = (sf i).val at hs
  have hmem : s ∈ idealAnnihilatorSections j F (iSup W) := by
    intro V hV b
    apply A.eq_of_locally_eq' (fun i ↦ V ⊓ W i) V
      (fun i ↦ homOfLE inf_le_left) (by
        intro x hx
        obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hV hx)
        exact Opens.mem_iSup.mpr ⟨i, hx, hi⟩) _ 0
    intro i
    rw [map_zero, F.map_smul]
    have hh := (sf i).property (V ⊓ W i) inf_le_right
      (P.presheaf.map (homOfLE inf_le_left).op b)
    have hj : X.presheaf.map (homOfLE inf_le_left : V ⊓ W i ⟶ V).op
        (j.app V b) = j.app (V ⊓ W i) (P.presheaf.map (homOfLE inf_le_left).op b) := by
      exact (ConcreteCategory.congr_hom
        (j.mapPresheaf.naturality (homOfLE inf_le_left).op) b).symm
    have heq : F.presheaf.map (homOfLE inf_le_left : V ⊓ W i ⟶ V).op
        (F.presheaf.map (homOfLE hV).op s) =
        F.presheaf.map (homOfLE inf_le_right : V ⊓ W i ⟶ W i).op (sf i).val := by
      rw [← hs i]
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    rw [hj, heq]
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

/-- The actual subsheaf of sections annihilated locally by the ideal inclusion. 
(blueprint: lem-weil-pbc-ideal-power-annihilator-quasicoherent)
-/
noncomputable def idealAnnihilator {X : Scheme.{u}} {P : X.Modules}
    (j : P ⟶ SheafOfModules.unit X.ringCatSheaf) (F : X.Modules) : X.Modules :=
  ⟨(idealAnnihilatorPresheaf j F).toPresheafOfModules,
    idealAnnihilatorPresheaf_isSheaf j F⟩

/-- The inclusion of the canonical annihilator subsheaf. 
(blueprint: lem-weil-pbc-ideal-power-annihilator-quasicoherent)
-/
noncomputable def idealAnnihilatorι {X : Scheme.{u}} {P : X.Modules}
    (j : P ⟶ SheafOfModules.unit X.ringCatSheaf) (F : X.Modules) :
    idealAnnihilator j F ⟶ F :=
  ⟨(idealAnnihilatorPresheaf j F).ι⟩

instance {X : Scheme.{u}} {P : X.Modules}
    (j : P ⟶ SheafOfModules.unit X.ringCatSheaf) (F : X.Modules) :
    Mono (idealAnnihilatorι j F) :=
  (Modules.toPresheafOfModules X).mono_of_mono_map (by
    change Mono (idealAnnihilatorPresheaf j F).ι
    infer_instance)

set_option backward.isDefEq.respectTransparency false in
/-- The section range of a quasi-coherent module map to the unit localizes on basic opens. -/
private theorem range_ideal_basicOpen {X : Scheme.{u}} {P : X.Modules}
    (j : P ⟶ SheafOfModules.unit X.ringCatSheaf) [P.IsQuasicoherent]
    (U : X.affineOpens) (f : Γ(X, U.1)) :
    Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
        (LinearMap.range (j.val.app (op U.1)).hom) =
      LinearMap.range (j.val.app (op (X.basicOpen f))).hom := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    rintro _ ⟨b, rfl⟩
    refine ⟨P.presheaf.map (homOfLE (X.basicOpen_le f)).op b, ?_⟩
    exact ConcreteCategory.congr_hom
      (j.mapPresheaf.naturality (homOfLE (X.basicOpen_le f)).op) b
  · rintro _ ⟨b, rfl⟩
    obtain ⟨k, t, ht⟩ := Modules.exists_map_eq_pow_smul_of_isAffineOpen P U.2 f b
    let K := Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
      (LinearMap.range (j.val.app (op U.1)).hom)
    have hmem : (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) ^ k *
        (show Γ(X, X.basicOpen f) from j.app (X.basicOpen f) b) ∈ K := by
      have h := Ideal.mem_map_of_mem
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
        (show j.app U.1 t ∈ LinearMap.range (j.val.app (op U.1)).hom from ⟨t, rfl⟩)
      have hn : X.presheaf.map (homOfLE (X.basicOpen_le f)).op
          (j.app U.1 t) = j.app (X.basicOpen f)
            (P.presheaf.map (homOfLE (X.basicOpen_le f)).op t) :=
        (ConcreteCategory.congr_hom
          (j.mapPresheaf.naturality (homOfLE (X.basicOpen_le f)).op) t).symm
      rw [hn, ht, Modules.Hom.app_smul] at h
      exact h
    exact (K.unit_mul_mem_iff_mem ((X.toRingedSpace.isUnit_res_basicOpen f).pow k)).mp hmem

set_option backward.isDefEq.respectTransparency false in
/-- Convert finite affine ranges into ideal data and apply the affine annihilator theorem. -/
private theorem annihilator_quasicoherent_of_affine_fg {X : Scheme.{u}} {P : X.Modules}
    (j : P ⟶ SheafOfModules.unit X.ringCatSheaf) [P.IsQuasicoherent]
    (hfg : ∀ U : X.affineOpens, (LinearMap.range (j.val.app (op U.1)).hom).FG)
    (F : X.Modules) [F.IsQuasicoherent] : (idealAnnihilator j F).IsQuasicoherent := by
  let J : X.IdealSheafData :=
    { ideal := fun U ↦ LinearMap.range (j.val.app (op U.1)).hom
      map_ideal_basicOpen := range_ideal_basicOpen j }
  have hJqc : J.toModules.IsQuasicoherent := Modules.ideal_qc J _ (Iso.refl _)
  have hfinite (U : X.affineOpens) : Module.Finite Γ(X, U.1) Γ(J.toModules, U.1) := by
    let q := (J.toModulesι.val.app (op U.1)).hom
    have hR : q.range = J.ideal U := SetLike.coe_injective (J.range_toModulesι_app U)
    have : Module.Finite Γ(X, U.1) q.range := by
      rw [hR]
      exact Module.Finite.of_fg (hfg U)
    exact (q.rangeRestrict.finite_iff_of_bijective
      ⟨fun a b h ↦ J.injective_toModulesι_app U.1 (congrArg Subtype.val h),
        fun ⟨a, b, hb⟩ ↦ ⟨b, Subtype.ext hb⟩⟩).mpr
      (show Module.Finite Γ(X, U.1) q.range from inferInstance)
  have : J.toModules.IsFiniteType :=
    (((Modules.quasicoherent_finite_type_affine.{u, u} X).2 J.toModules hJqc).2.1
      X.affineOpens (fun U ↦ U.1) (iSup_affineOpens_eq_top X) (fun U ↦ U.2) hfinite).1
  apply AlgebraicGeometry.annihilator_subsheaf_quasicoherent X J F
    (idealAnnihilator j F) (idealAnnihilatorι j F)
  intro U s
  change (∃ t : idealAnnihilatorSections j F U.1, t.val = s) ↔
    ∀ a ∈ J.ideal U, a • s = 0
  constructor
  · rintro ⟨t, rfl⟩ a ⟨b, rfl⟩
    have ht := t.property U.1 le_rfl b
    change (show Γ(X, U.1) from j.app U.1 b) • t.val = 0
    change (show Γ(X, U.1) from j.app U.1 b) •
      F.presheaf.map (𝟙 (op U.1)) t.val = 0 at ht
    rwa [F.presheaf.map_id, ConcreteCategory.id_apply] at ht
  · intro hs
    refine ⟨⟨s, ?_⟩, rfl⟩
    intro V hV b
    let A : TopCat.Sheaf Ab X := ⟨F.presheaf, F.isSheaf⟩
    let K := {W : X.affineOpens // W.1 ≤ V}
    refine A.eq_of_locally_eq' (fun W : K ↦ W.val.val) V
      (fun W ↦ homOfLE W.property) ?_ _ 0 ?_
    · intro x hx
      obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hx
      exact Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWV⟩, hxW⟩
    · intro W
      rw [map_zero, F.map_smul]
      have hb : X.presheaf.map (homOfLE W.property).op (j.app V b) ∈ J.ideal W.val := by
        refine ⟨P.presheaf.map (homOfLE W.property).op b, ?_⟩
        exact ConcreteCategory.congr_hom
          (j.mapPresheaf.naturality (homOfLE W.property).op) b
      let t : Γ(F, W.val.val) := F.presheaf.map (homOfLE (W.property.trans hV)).op s
      let L : Ideal Γ(X, W.val.val) :=
        LinearMap.ker (LinearMap.toSpanSingleton Γ(X, W.val.val) Γ(F, W.val.val) t)
      have hle : J.ideal W.val ≤ L := by
        rw [← J.map_ideal (W.property.trans hV), Ideal.map_le_iff_le_comap]
        intro a ha
        change X.presheaf.map (homOfLE (W.property.trans hV)).op a • t = 0
        dsimp only [t]
        rw [← F.map_smul, hs a ha, map_zero]
      have hkill := hle hb
      change X.presheaf.map (homOfLE W.property).op (j.app V b) • t = 0 at hkill
      convert hkill using 1
      dsimp only [t]
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl

/-- The annihilator of each power of a finite-type quasi-coherent ideal is quasi-coherent.

Source: Stacks Project, Properties, Tag 01PO, proof of (1), applied to the powers
in the proof of Tag 01PQ.
(blueprint: lem-weil-pbc-ideal-power-annihilator-quasicoherent).

Proof: On an affine open Spec R identify I with a finitely generated ideal J and
F with the sheaf associated to an R-module M. The recursive image construction
of ideal powers gives J^n, which is finitely generated, including J^0 = R.
The canonical subsheaf has sections killed by J^n: annihilation on the affine
open implies annihilation on every smaller affine open by localization, and
these smaller affines cover any open. Put N = {m in M | J^n m = 0}. For a
principal open D(f), localization of N injects into M_f. If m/f^r is killed
by (J^n)_f, choose finite generators of J^n and clear a power of f in each
annihilation equation. Their maximum e gives f^e m in N, showing that
m/f^r belongs to N_f. With no generators, take e = 0. Thus the canonical
annihilator is the sheaf associated to N on every affine open; the inclusions
into F make these local identifications compatible. It is quasi-coherent.
-/
theorem ideal_power_annihilator_quasicoherent {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]
    [I.IsQuasicoherent] [I.IsFiniteType] (F : X.Modules) [F.IsQuasicoherent]
    (n : ℕ) : (idealAnnihilator (idealSheafPower ι n).2 F).IsQuasicoherent := by
  have hp := Modules.powers_affine_sections ι n
  have : (idealSheafPower ι n).1.IsQuasicoherent := hp.1
  apply annihilator_quasicoherent_of_affine_fg (idealSheafPower ι n).2 _ F
  intro U
  rw [hp.2 U]
  have : Module.Finite Γ(X, U.1) Γ(I, U.1) :=
    Modules.finite_sections_of_finiteType I U.2
  let q : Γ(I, U.1) →ₗ[Γ(X, U.1)] Γ(X, U.1) := (ι.val.app (op U.1)).hom
  exact (Submodule.fg_range q).pow n

end AlgebraicGeometry.Scheme
