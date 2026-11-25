/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Ideal.Operations
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.CategoryTheory.Subobject.Basic

/-! # Comparing ideal-data powers with recursive image powers

Source: Stacks Project, Schemes, Tags 01I8 and 01IC, ideal products on affine opens.
(blueprint: lem-pc-ideal-data-recursive-power-comparison)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

private theorem idealData_quasicoherent {X : Scheme.{u}} (J : X.IdealSheafData) :
    J.toModules.IsQuasicoherent := by
  have := SheafOfModules.isQuasicoherent_unit (R := J.subscheme.ringCatSheaf)
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf)
      ((SheafOfModules.pushforward J.subschemeι.toRingCatSheafHom).obj
        (SheafOfModules.unit J.subscheme.ringCatSheaf)) :=
    isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated J.subschemeι _
  exact isQuasicoherent_kernel J.toPushforwardSubscheme

open MonoidalCategory CategoryTheory.Limits Opposite in
set_option backward.isDefEq.respectTransparency false in
private theorem product_qc {X : Scheme.{u}} {K : X.Modules}
    (i : K ⟶ SheafOfModules.unit X.ringCatSheaf) (M : X.Modules)
    [K.IsQuasicoherent] [M.IsQuasicoherent] :
    (idealModuleProduct i M).IsQuasicoherent := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  have := (quasiCoherent_tensor_product_affine_sections K M).1
  let a := i ▷ M ≫ (λ_ M).hom
  have := isQuasicoherent_cokernel a
  have := isQuasicoherent_kernel (cokernel.π a)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Abelian.imageIsoImage a) inferInstance

open MonoidalCategory CategoryTheory.Limits Opposite in
open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
private theorem multiplication_range {X : Scheme.{u}} {K : X.Modules}
    (i : K ⟶ SheafOfModules.unit X.ringCatSheaf) (M : X.Modules)
    [K.IsQuasicoherent] [M.IsQuasicoherent] (U : X.affineOpens) :
    let I : Ideal Γ(X, U.1) := LinearMap.range (i.val.app (op U.1)).hom
    Set.range ((idealModuleProductι i M).app U.1) =
      {s | s ∈ I • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1))} := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  let a := i ▷ M ≫ (λ_ M).hom
  have := (quasiCoherent_tensor_product_affine_sections K M).1
  have ht := (quasiCoherent_tensor_product_affine_sections K M).2 U.1 U.2
  let I : Ideal Γ(X, U.1) := LinearMap.range (i.val.app (op U.1)).hom
  have hp (s : Γ(K, U.1)) (t : Γ(M, U.1)) :
      a.app U.1 (tensorSectionsMap K M U.1 (s ⊗ₜ t)) = (show Γ(X, U.1) from i.app U.1 s) • t := by
    rw [tensorSectionsMap_tmul]
    change (λ_ M).hom.app U.1 ((i ▷ M).app U.1 (tmulSection s t)) = _
    rw [whiskerRight_app_tmulSection, leftUnitor_hom_app_tmulSection']
    rfl
  have ha : LinearMap.range (a.val.app (op U.1)).hom = I • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)) := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      obtain ⟨w, rfl⟩ := ht.2 z
      induction w using TensorProduct.inductionOn with
      | tmul s t =>
        change a.app U.1 (tensorSectionsMap K M U.1 (s ⊗ₜ t)) ∈ I • ⊤
        rw [hp]
        exact Submodule.smul_mem_smul ⟨s, rfl⟩ (Submodule.mem_top)
      | add x y hx hy =>
        simp only [map_add]
        exact Submodule.add_mem _ hx hy
    · apply Submodule.smul_le.mpr
      intro r hr t _
      obtain ⟨s, rfl⟩ := hr
      exact ⟨tensorSectionsMap K M U.1 (s ⊗ₜ t), hp s t⟩
  have hb := (quasiCoherent_cokernel_image a).2.2.2.2.2.2.2.2 U
  have hi : Set.range ((idealModuleProductι i M).app U.1) =
      Set.range ((Abelian.image.ι a).app U.1) := by
    let e := Abelian.imageIsoImage a
    ext s
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨e.inv.app U.1 t, ?_⟩
      have h : e.inv ≫ Abelian.image.ι a = image.ι a := by
        calc
          _ = e.inv ≫ e.hom ≫ image.ι a :=
            congrArg (fun f ↦ e.inv ≫ f)
              (Abelian.imageIsoImage_hom_comp_image_ι a).symm
          _ = _ := by simp
      exact congrArg (fun f ↦ f.app U.1 t) h
    · rintro ⟨t, rfl⟩
      refine ⟨e.hom.app U.1 t, ?_⟩
      exact congrArg (fun f ↦ f.app U.1 t)
        (Abelian.imageIsoImage_hom_comp_image_ι a)
  rw [hi, hb.1]
  exact congrArg (fun P : Submodule Γ(X, U.1) Γ(M, U.1) ↦ (P : Set Γ(M, U.1))) ha


open CategoryTheory.Limits Opposite in
set_option backward.isDefEq.respectTransparency false in
private theorem product_range {X : Scheme.{u}} (J : X.IdealSheafData)
    (M : X.Modules) [M.IsQuasicoherent] (U : X.affineOpens) :
    LinearMap.range ((idealModuleProductι J.toModulesι M).val.app (op U.1)).hom =
      J.ideal U • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)) := by
  have := idealData_quasicoherent J
  have hI : (LinearMap.range (J.toModulesι.val.app (op U.1)).hom : Ideal Γ(X, U.1)) =
      J.ideal U := SetLike.coe_injective (J.range_toModulesι_app U)
  apply SetLike.coe_injective
  exact hI ▸ multiplication_range J.toModulesι M U

open CategoryTheory.Limits Opposite in
set_option backward.isDefEq.respectTransparency false in
private theorem powers_qc {X : Scheme.{u}} {K : X.Modules}
    (i : K ⟶ SheafOfModules.unit X.ringCatSheaf) [K.IsQuasicoherent] (n : ℕ) :
    (idealSheafPower i n).1.IsQuasicoherent := by
  induction n using Nat.twoStepInduction with
  | zero =>
    exact SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  | one => assumption
  | more n _ ih => exact product_qc i _

open CategoryTheory.Limits Opposite in
set_option backward.isDefEq.respectTransparency false in
private theorem powers_range {X : Scheme.{u}} (J : X.IdealSheafData)
    (U : X.affineOpens) : ∀ n : ℕ, 0 < n →
    (LinearMap.range ((idealSheafPower J.toModulesι n).2.val.app (op U.1)).hom :
      Ideal Γ(X, U.1)) = J.ideal U ^ n := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction k with
  | zero =>
    simpa only [Nat.add_zero, idealSheafPower, pow_one] using
      SetLike.coe_injective (J.range_toModulesι_app U)
  | succ k ih =>
    rw [show 1 + (k + 1) = k + 2 by omega]
    change LinearMap.range ((idealModuleProductι J.toModulesι
      (idealSheafPower J.toModulesι (k + 1)).1 ≫
      (idealSheafPower J.toModulesι (k + 1)).2).val.app (op U.1)).hom = _
    have := idealData_quasicoherent J
    have := powers_qc J.toModulesι (k + 1)
    change LinearMap.range
      (((idealSheafPower J.toModulesι (k + 1)).2.val.app (op U.1)).hom.comp
        ((idealModuleProductι J.toModulesι
          (idealSheafPower J.toModulesι (k + 1)).1).val.app (op U.1)).hom) = _
    rw [LinearMap.range_comp, product_range, Submodule.map_smul'', Submodule.map_top]
    have ih' : (LinearMap.range
        ((idealSheafPower J.toModulesι (k + 1)).2.val.app (op U.1)).hom :
          Ideal Γ(X, U.1)) = J.ideal U ^ (k + 1) := by
      change (LinearMap.range
        ((idealSheafPower J.toModulesι (1 + k)).2.val.app (op U.1)).hom :
          Ideal Γ(X, U.1)) = J.ideal U ^ (1 + k) at ih
      rw [Nat.add_comm 1 k] at ih
      exact ih
    rw [ih', Ideal.smul_eq_mul]
    exact (pow_succ' (J.ideal U) (k + 1)).symm

private theorem hom_zero_of_affine {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) (h : ∀ V : X.affineOpens, ∀ s : Γ(M, V.1), φ.app V.1 s = 0) :
    φ = 0 := by
  apply hom_ext
  intro W
  ext s
  change φ.app W s = 0
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩
    (fun i : {V : X.affineOpens // V.1 ≤ W} ↦ i.1.1) W
    (fun i ↦ homOfLE i.2) ?_ _ _ ?_
  · intro x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVW⟩, hxV⟩
  · intro i
    have hn := congrArg (fun f ↦ f s)
      (φ.val.naturality (homOfLE i.2).op)
    change φ.app i.1.1 (M.presheaf.map (homOfLE i.2).op s) =
      N.presheaf.map (homOfLE i.2).op (φ.app W s) at hn
    rw [← hn, h, map_zero]

private theorem subobject_le_of_affine_range {X : Scheme.{u}} {M N P : X.Modules}
    (i : M ⟶ P) (j : N ⟶ P) [Mono i] [Mono j]
    (h : ∀ V : X.affineOpens, Set.range (i.app V.1) ⊆ Set.range (j.app V.1)) :
    Subobject.mk i ≤ Subobject.mk j := by
  have hz : i ≫ Limits.cokernel.π j = 0 := by
    apply hom_zero_of_affine
    intro V s
    obtain ⟨t, ht⟩ := h V ⟨s, rfl⟩
    change (Limits.cokernel.π j).app V.1 (i.app V.1 s) = 0
    rw [← ht]
    exact congrArg (fun q ↦ q.app V.1 t) (Limits.cokernel.condition j)
  let k : M ⟶ Abelian.image j := Limits.kernel.lift (Limits.cokernel.π j) i hz
  let l : M ⟶ N := k ≫ inv (Abelian.factorThruImage j)
  apply Subobject.mk_le_mk_of_comm l
  change k ≫ inv (Abelian.factorThruImage j) ≫ j = i
  calc
    k ≫ inv (Abelian.factorThruImage j) ≫ j =
        k ≫ inv (Abelian.factorThruImage j) ≫
          Abelian.factorThruImage j ≫ Abelian.image.ι j :=
      congrArg (fun q ↦ k ≫ inv (Abelian.factorThruImage j) ≫ q)
        (Abelian.image.fac j).symm
    _ = k ≫ Abelian.image.ι j := by rw [IsIso.inv_hom_id_assoc]
    _ = i := Limits.kernel.lift_ι _ _ hz

private theorem power_mono {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ) :
    Mono (idealSheafPower I.toModulesι n).2 := by
  induction n using Nat.twoStepInduction with
  | zero => simp only [idealSheafPower]; infer_instance
  | one => simp only [idealSheafPower]; infer_instance
  | more n _ ih =>
    change Mono (idealModuleProductι I.toModulesι _ ≫ _)
    have : Mono (idealModuleProductι I.toModulesι
        (idealSheafPower I.toModulesι (n + 1)).1) := by
      dsimp [idealModuleProductι]
      infer_instance
    have := ih
    infer_instance

/-- Ideal-data powers are quasi-coherent and agree with recursive image powers.

Source: Stacks Project, Schemes, Tags 01I8 and 01IC, ideal products on affine opens.
(blueprint: lem-pc-ideal-data-recursive-power-comparison)

Proof: The ideal module is quasi-coherent: locally on an affine it is the tilde
module of the specified ideal. This applies to every ideal-data power. Both
inclusions are monomorphisms. On an affine open with ring A the
ideal-data power has image I(A)^n, by the affine sections formula for toModules.
The recursive power has the same image: at n = 0 its inclusion is the identity,
at n = 1 it is the original ideal, and each later multiplication image has
sections the product of the two ideals, by exactness of affine sections on
quasi-coherent modules and the affine tensor-sections comparison. Induction
therefore gives I(A)^n. Equality of submodules on an affine basis gives equality
as subobjects of the structure module, and the canonical isomorphism of the
monomorphic representatives has the displayed compatibility with inclusions.
This also covers n = 0, the zero ideal, the unit ideal, and the empty scheme. -/
theorem idealData_recursive_power_comparison {X : Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) :
    (I ^ n).toModules.IsQuasicoherent ∧
      ∃ e : (I ^ n).toModules ≅ (idealSheafPower I.toModulesι n).1,
        e.hom ≫ (idealSheafPower I.toModulesι n).2 = (I ^ n).toModulesι := by
  have hqc := idealData_quasicoherent (I ^ n)
  have : Mono (idealSheafPower I.toModulesι n).2 := power_mono I n
  have hr (U : X.affineOpens) :
      Set.range ((I ^ n).toModulesι.app U.1) =
        Set.range ((idealSheafPower I.toModulesι n).2.app U.1) := by
    rw [(I ^ n).range_toModulesι_app]
    cases n with
    | zero => simp [idealSheafPower]
    | succ n =>
      have h := congrArg (fun J : Ideal Γ(X, U.1) ↦ (J : Set Γ(X, U.1)))
        (powers_range I U (n + 1) (by omega))
      exact h.symm
  have heq : Subobject.mk (I ^ n).toModulesι =
      Subobject.mk (idealSheafPower I.toModulesι n).2 :=
    le_antisymm
      (subobject_le_of_affine_range _ _ (fun U ↦ (hr U).subset))
      (subobject_le_of_affine_range _ _ (fun U ↦ (hr U).symm.subset))
  refine ⟨hqc, Subobject.isoOfMkEqMk _ _ heq, ?_⟩
  exact Subobject.ofMkLEMk_comp heq.le

end AlgebraicGeometry.Scheme.Modules
