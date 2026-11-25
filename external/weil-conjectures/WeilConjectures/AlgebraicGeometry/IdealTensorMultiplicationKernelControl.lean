/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentAffineSectionsFinite
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import Mathlib.RingTheory.TensorProduct.Finite
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian

/-! # Coherence and annihilation of the ideal tensor multiplication kernel

Source: Stacks Project, Tag 01YB, second Artin-Rees argument.
(blueprint: lem-pc-ideal-tensor-multiplication-kernel-control)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

private theorem kernel_control_ideal_qc {X : Scheme.{u}} (J : X.IdealSheafData) :
    J.toModules.IsQuasicoherent := by
  have := SheafOfModules.isQuasicoherent_unit (R := J.subscheme.ringCatSheaf)
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf)
      ((SheafOfModules.pushforward J.subschemeι.toRingCatSheafHom).obj
        (SheafOfModules.unit J.subscheme.ringCatSheaf)) :=
    isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated J.subschemeι _
  exact isQuasicoherent_kernel J.toPushforwardSubscheme

open MonoidalCategory in
set_option backward.isDefEq.respectTransparency false in
private theorem kernel_control_product_qc {X : Scheme.{u}} {K : X.Modules}
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

open MonoidalCategory in
open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
private theorem kernel_control_multiplication_range {X : Scheme.{u}} {K : X.Modules}
    (i : K ⟶ SheafOfModules.unit X.ringCatSheaf) (M : X.Modules)
    [K.IsQuasicoherent] [M.IsQuasicoherent] (U : X.affineOpens) :
    let I : Ideal Γ(X, U.1) := LinearMap.range (i.val.app (Opposite.op U.1)).hom
    Set.range ((idealModuleProductι i M).app U.1) =
      {s | s ∈ I • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1))} := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  let a := i ▷ M ≫ (λ_ M).hom
  have := (quasiCoherent_tensor_product_affine_sections K M).1
  have ht := (quasiCoherent_tensor_product_affine_sections K M).2 U.1 U.2
  let I : Ideal Γ(X, U.1) := LinearMap.range (i.val.app (Opposite.op U.1)).hom
  have hp (s : Γ(K, U.1)) (t : Γ(M, U.1)) :
      a.app U.1 (tensorSectionsMap K M U.1 (s ⊗ₜ t)) = (show Γ(X, U.1) from i.app U.1 s) • t := by
    rw [tensorSectionsMap_tmul]
    change (λ_ M).hom.app U.1 ((i ▷ M).app U.1 (tmulSection s t)) = _
    rw [whiskerRight_app_tmulSection, leftUnitor_hom_app_tmulSection']
    rfl
  have ha : LinearMap.range (a.val.app (Opposite.op U.1)).hom =
      I • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)) := by
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


set_option backward.isDefEq.respectTransparency false in
private theorem kernel_control_product_range {X : Scheme.{u}} (J : X.IdealSheafData)
    (M : X.Modules) [M.IsQuasicoherent] (U : X.affineOpens) :
    LinearMap.range ((idealModuleProductι J.toModulesι M).val.app (Opposite.op U.1)).hom =
      J.ideal U • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)) := by
  have := kernel_control_ideal_qc J
  have hI : (LinearMap.range (J.toModulesι.val.app (Opposite.op U.1)).hom : Ideal Γ(X, U.1)) =
      J.ideal U := SetLike.coe_injective (J.range_toModulesι_app U)
  apply SetLike.coe_injective
  exact hI ▸ kernel_control_multiplication_range J.toModulesι M U

set_option backward.isDefEq.respectTransparency false in
private theorem kernel_control_powers_qc {X : Scheme.{u}} {K : X.Modules}
    (i : K ⟶ SheafOfModules.unit X.ringCatSheaf) [K.IsQuasicoherent] (n : ℕ) :
    (idealSheafPower i n).1.IsQuasicoherent := by
  induction n using Nat.twoStepInduction with
  | zero =>
    exact SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  | one => assumption
  | more n _ ih => exact kernel_control_product_qc i _

set_option backward.isDefEq.respectTransparency false in
private theorem kernel_control_powers_range {X : Scheme.{u}} (J : X.IdealSheafData)
    (U : X.affineOpens) : ∀ n : ℕ, 0 < n →
    (LinearMap.range ((idealSheafPower J.toModulesι n).2.val.app (Opposite.op U.1)).hom :
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
      (idealSheafPower J.toModulesι (k + 1)).2).val.app (Opposite.op U.1)).hom = _
    have := kernel_control_ideal_qc J
    have := kernel_control_powers_qc J.toModulesι (k + 1)
    change LinearMap.range
      (((idealSheafPower J.toModulesι (k + 1)).2.val.app (Opposite.op U.1)).hom.comp
        ((idealModuleProductι J.toModulesι
          (idealSheafPower J.toModulesι (k + 1)).1).val.app (Opposite.op U.1)).hom) = _
    rw [LinearMap.range_comp, kernel_control_product_range, Submodule.map_smul'', Submodule.map_top]
    have ih' : (LinearMap.range
        ((idealSheafPower J.toModulesι (k + 1)).2.val.app (Opposite.op U.1)).hom :
          Ideal Γ(X, U.1)) = J.ideal U ^ (k + 1) := by
      change (LinearMap.range
        ((idealSheafPower J.toModulesι (1 + k)).2.val.app (Opposite.op U.1)).hom :
          Ideal Γ(X, U.1)) = J.ideal U ^ (1 + k) at ih
      rw [Nat.add_comm 1 k] at ih
      exact ih
    rw [ih', Ideal.smul_eq_mul]
    exact (pow_succ' (J.ideal U) (k + 1)).symm


set_option backward.isDefEq.respectTransparency false in
private theorem ideal_tensor_balancing {X : Scheme.{u}} (J : X.IdealSheafData)
    (H : X.Modules) (U : X.Opens) (a b : Γ(J.toModules, U)) (h : Γ(H, U)) :
    (show Γ(X, U) from J.toModulesι.app U a) • tmulSection b h =
      tmulSection a ((show Γ(X, U) from J.toModulesι.app U b) • h) := by
  have he : (show Γ(X, U) from J.toModulesι.app U a) • b =
      (show Γ(X, U) from J.toModulesι.app U b) • a := by
    apply J.injective_toModulesι_app U
    rw [Hom.app_smul, Hom.app_smul]
    change (show Γ(X, U) from J.toModulesι.app U a) *
      (show Γ(X, U) from J.toModulesι.app U b) =
      (show Γ(X, U) from J.toModulesι.app U b) *
      (show Γ(X, U) from J.toModulesι.app U a)
    exact mul_comm _ _
  rw [← smul_tmulSection, he, smul_tmulSection, tmulSection_smul]


set_option backward.isDefEq.respectTransparency false in
/-- The tensor multiplication source is coherent and its quasi-coherent kernel is
annihilated by the same ideal power.
Source: Stacks Project, Tag 01YB, the short exact sequence preceding the second
Artin-Rees application; Tags 01XZ and 01Y0 for coherence.
(blueprint: lem-pc-ideal-tensor-multiplication-kernel-control)

Proof: On an affine open, the ideal power is a finite module over a Noetherian ring,
and the sections of H are finite. Their tensor product is finite. The affine tensor
comparison gives quasi-coherence and finite type, hence coherence of T = I^n tensor H.
The coherent kernel theorem gives coherence, and hence quasi-coherence, of K = ker(mu).
For a section z of K, write its image as a sum b_j tensor h_j, with sum b_j h_j = 0.
For a in I^n, balancing and commutativity give
 a (sum b_j tensor h_j) = sum a tensor (b_j h_j) = 0.
The kernel inclusion is injective, so a z = 0. The affine product formula identifies
I^n K with zero. The recursive sheaf power has affine range I(U)^n, including n=0,
when it is the structure sheaf; thus this is the stated product vanishing.
Vanishing on the affine basis implies vanishing of the product sheaf.
For n=0 multiplication is the left unitor up to the canonical unit-ideal isomorphism,
so K=0. Zero and unit ideals and the zero module satisfy the same calculation. -/
theorem ideal_tensor_multiplication_kernel_control
    {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (H : X.Modules)
    (hH : RingedSpace.IsCoherent X.toRingedSpace H) (n : ℕ) :
    letI : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    let T := (I ^ n).toModules ⊗ H
    let μ := (I ^ n).toModulesι ▷ H ≫ (λ_ H).hom
    RingedSpace.IsCoherent X.toRingedSpace T ∧
      (kernel μ).IsQuasicoherent ∧
      IsZero (idealModuleProduct (idealSheafPower I.toModulesι n).2 (kernel μ)) := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  let J := I ^ n
  let T := J.toModules ⊗ H
  let μ : T ⟶ H := J.toModulesι ▷ H ≫ (λ_ H).hom
  have : H.IsQuasicoherent :=
    ((isCoherent_iff_isQuasicoherent_and_isFiniteType X H).mp hH).1
  have : J.toModules.IsQuasicoherent := kernel_control_ideal_qc J
  have hTq : T.IsQuasicoherent :=
    (quasiCoherent_tensor_product_affine_sections J.toModules H).1
  have hTf (U : X.affineOpens) : Module.Finite Γ(X, U.1) Γ(T, U.1) := by
    have := IsLocallyNoetherian.component_noetherian U
    have : _root_.IsNoetherian Γ(X, U.1) Γ(X, U.1) := inferInstance
    let j : Γ(J.toModules, U.1) →ₗ[Γ(X, U.1)] Γ(X, U.1) :=
      (unitSectionsEquiv U.1).symm.toLinearMap.comp
        (J.toModulesι.val.app (.op U.1)).hom
    have : Module.Finite Γ(X, U.1) Γ(J.toModules, U.1) :=
      Module.Finite.of_injective j
        ((unitSectionsEquiv U.1).symm.injective.comp (J.injective_toModulesι_app U.1))
    have : Module.Finite Γ(X, U.1) Γ(H, U.1) :=
      coherent_affine_sections_finite X H hH U.1 U.2
    exact Module.Finite.of_surjective (tensorSectionsMap J.toModules H U.1)
      ((quasiCoherent_tensor_product_affine_sections J.toModules H).2 U.1 U.2).2
  have hTc : RingedSpace.IsCoherent X.toRingedSpace T :=
    (isCoherent_iff_isQuasicoherent_and_isFiniteType X T).mpr
      ⟨hTq, (((quasicoherent_finite_type_affine.{u, u} X).2 T hTq).2.1
        X.affineOpens (fun U ↦ U.1) (iSup_affineOpens_eq_top X) (fun U ↦ U.2) hTf).1⟩
  have : T.IsQuasicoherent := hTq
  have hKq : (kernel μ).IsQuasicoherent := isQuasicoherent_kernel μ
  have : (kernel μ).IsQuasicoherent := hKq
  have hkill (U : X.affineOpens) (r : Γ(X, U.1)) (hr : r ∈ I.ideal U ^ n) :
      ∀ k : Γ(kernel μ, U.1), r • k = 0 := by
    intro k
    have hr' : r ∈ J.ideal U := by simpa [J] using hr
    obtain ⟨a, ha⟩ := (Set.ext_iff.mp (J.range_toModulesι_app U) r).mpr hr'
    let κ := kernel.ι μ
    have hμ (b : Γ(J.toModules, U.1)) (h : Γ(H, U.1)) :
        μ.app U.1 (tmulSection b h) =
          (show Γ(X, U.1) from J.toModulesι.app U.1 b) • h := by
      change (λ_ H).hom.app U.1 ((J.toModulesι ▷ H).app U.1 (tmulSection b h)) = _
      rw [whiskerRight_app_tmulSection, leftUnitor_hom_app_tmulSection']
      rfl
    let L : Γ(H, U.1) →ₗ[Γ(X, U.1)] Γ(T, U.1) :=
      (tensorSectionsMap J.toModules H U.1).comp ((TensorProduct.mk Γ(X, U.1) _ _) a)
    have hb (z : Γ(T, U.1)) : r • z = L (μ.app U.1 z) := by
      obtain ⟨w, rfl⟩ :=
        ((quasiCoherent_tensor_product_affine_sections J.toModules H).2 U.1 U.2).2 z
      induction w using TensorProduct.inductionOn with
      | tmul b h =>
        -- Expose the linear map so that its value is computed by tensorSectionsMap_tmul.
        simp only [L, tensorSectionsMap_tmul, hμ]
        rw [← ha]
        exact ideal_tensor_balancing J H U.1 a b h
      | add x y hx hy => simp only [map_add, smul_add, hx, hy]
    apply injective_map_kernelι U.1 μ
    change κ.app U.1 (r • k) = κ.app U.1 0
    rw [Hom.app_smul, hb]
    have hk : μ.app U.1 (κ.app U.1 k) = 0 := by
      exact congrArg (fun f ↦ f.app U.1 k) (kernel.condition μ)
    rw [hk, map_zero]
    exact (κ.app U.1).hom.map_zero.symm
  let P := (idealSheafPower I.toModulesι n).1
  let ι := (idealSheafPower I.toModulesι n).2
  have : I.toModules.IsQuasicoherent := kernel_control_ideal_qc I
  have : P.IsQuasicoherent := kernel_control_powers_qc I.toModulesι n
  let ν : P ⊗ kernel μ ⟶ kernel μ := ι ▷ kernel μ ≫ (λ_ (kernel μ)).hom
  have hzero (U : X.affineOpens) (z : Γ(P ⊗ kernel μ, U.1)) : ν.app U.1 z = 0 := by
    obtain ⟨w, rfl⟩ :=
      ((quasiCoherent_tensor_product_affine_sections P (kernel μ)).2 U.1 U.2).2 z
    induction w using TensorProduct.inductionOn with
    | tmul a k =>
      rw [tensorSectionsMap_tmul]
      change (λ_ (kernel μ)).hom.app U.1 ((ι ▷ kernel μ).app U.1
        (tmulSection a k)) = 0
      rw [whiskerRight_app_tmulSection, leftUnitor_hom_app_tmulSection']
      apply hkill U
      cases n with
      | zero => simp
      | succ m =>
        have hrange := kernel_control_powers_range I U (m + 1) (by omega)
        have ha : (show Γ(X, U.1) from ι.app U.1 a) ∈
            LinearMap.range ((idealSheafPower I.toModulesι (m + 1)).2.val.app
              (Opposite.op U.1)).hom := ⟨a, rfl⟩
        rw [hrange] at ha
        change (show Γ(X, U.1) from ι.app U.1 a) ∈ I.ideal U ^ (m + 1)
        exact ha
    | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  have hν : ν = 0 := by
    apply hom_ext
    intro W
    ext z
    change ν.app W z = 0
    refine TopCat.Sheaf.eq_of_locally_eq' ⟨(kernel μ).presheaf, (kernel μ).isSheaf⟩
      (fun V : {U : X.affineOpens // U.1 ≤ W} ↦ V.1.1) W
      (fun V ↦ homOfLE V.2) ?_ _ _ ?_
    · intro x hx
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨U, hU⟩, hUW⟩, hxU⟩
    · intro V
      rw [← Hom.app_presheaf_map, map_zero]
      exact hzero V.1 _
  refine ⟨hTc, hKq, ?_⟩
  change IsZero (image ν)
  apply IsZero.of_mono_eq_zero (image.ι ν)
  apply zero_of_epi_comp (factorThruImage ν)
  exact (image.fac ν).trans hν

end AlgebraicGeometry.Scheme.Modules

