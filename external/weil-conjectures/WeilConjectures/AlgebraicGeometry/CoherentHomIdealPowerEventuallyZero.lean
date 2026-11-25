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

import WeilConjectures.AlgebraicGeometry.CoherentAffineSectionsFinite
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentSupportPowerIdealKills
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.IdealPowerProductZeroAffineCover
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.Algebra.Homology.ModuleStalkExact

/-! # HOM ideal-power comparison over an open complement

Source: Stacks Project, Cohomology of Schemes, Lemma 01YB.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

open MonoidalCategory in
set_option backward.isDefEq.respectTransparency false in
private theorem product_qc {X : Scheme.{u}} {K : X.Modules}
    (i : K ⟶ SheafOfModules.unit X.ringCatSheaf) (M : X.Modules)
    [K.IsQuasicoherent] [M.IsQuasicoherent] :
    (idealModuleProduct i M).IsQuasicoherent := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  have := (Modules.quasiCoherent_tensor_product_affine_sections K M).1
  let a := i ▷ M ≫ (λ_ M).hom
  have := (Modules.quasiCoherent_cokernel_image a).2.2.2.2.2.2.2.1
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Abelian.imageIsoImage a) inferInstance

open MonoidalCategory in
open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
private theorem multiplication_range {X : Scheme.{u}} {K : X.Modules}
    (i : K ⟶ SheafOfModules.unit X.ringCatSheaf) (M : X.Modules)
    [K.IsQuasicoherent] [M.IsQuasicoherent] (U : X.affineOpens) :
    let I : Ideal Γ(X, U.1) := LinearMap.range (i.val.app (Opposite.op U.1)).hom
    Set.range ((idealModuleProductι i M).app U.1) =
      {s | s ∈ I • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1))} := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  let a := i ▷ M ≫ (λ_ M).hom
  have := (Modules.quasiCoherent_tensor_product_affine_sections K M).1
  have ht := (Modules.quasiCoherent_tensor_product_affine_sections K M).2 U.1 U.2
  let I : Ideal Γ(X, U.1) := LinearMap.range (i.val.app (Opposite.op U.1)).hom
  have hp (s : Γ(K, U.1)) (t : Γ(M, U.1)) :
      a.app U.1 (Modules.tensorSectionsMap K M U.1 (s ⊗ₜ t)) =
        (show Γ(X, U.1) from i.app U.1 s) • t := by
    rw [Modules.tensorSectionsMap_tmul]
    change (λ_ M).hom.app U.1 ((i ▷ M).app U.1 (Modules.tmulSection s t)) = _
    rw [Modules.whiskerRight_app_tmulSection, Modules.leftUnitor_hom_app_tmulSection']
    rfl
  have ha : LinearMap.range (a.val.app (Opposite.op U.1)).hom =
      I • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)) := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      obtain ⟨w, rfl⟩ := ht.2 z
      induction w using TensorProduct.inductionOn with
      | tmul s t =>
        change a.app U.1 (Modules.tensorSectionsMap K M U.1 (s ⊗ₜ t)) ∈ I • ⊤
        rw [hp]
        exact Submodule.smul_mem_smul ⟨s, rfl⟩ (Submodule.mem_top)
      | add x y hx hy =>
        simp only [map_add]
        exact Submodule.add_mem _ hx hy
    · apply Submodule.smul_le.mpr
      intro r hr t _
      obtain ⟨s, rfl⟩ := hr
      exact ⟨Modules.tensorSectionsMap K M U.1 (s ⊗ₜ t), hp s t⟩
  have hb := (Modules.quasiCoherent_cokernel_image a).2.2.2.2.2.2.2.2 U
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


/-- Sheaf separatedness detects a zero morphism on the affine basis.
Source: Stacks Project, proof of Lemma 01YB, affine-local detection of zero maps. -/
private theorem hom_zero_of_affine {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) (h : ∀ V : X.affineOpens, ∀ s : Γ(M, V.1), φ.app V.1 s = 0) :
    φ = 0 := by
  apply Modules.hom_ext
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
    rw [← Modules.Hom.app_presheaf_map, map_zero]
    exact h i.1 _


set_option backward.isDefEq.respectTransparency false in
private theorem power_qc {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ) :
    (idealSheafPower I.toModulesι n).1.IsQuasicoherent := by
  cases n with
  | zero => exact SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  | succ n =>
    have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
    exact (Modules.ideal_times_quasiCoherent_affine_sections I
      (SheafOfModules.unit X.ringCatSheaf)).2.2.1 _ (by omega)

set_option backward.isDefEq.respectTransparency false in
private theorem power_range {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ)
    (V : X.affineOpens) :
    (LinearMap.range ((idealSheafPower I.toModulesι n).2.val.app (Opposite.op V.1)).hom :
      Ideal Γ(X, V.1)) = I.ideal V ^ n := by
  apply SetLike.coe_injective
  cases n with
  | zero =>
    simp only [idealSheafPower, pow_zero, Ideal.one_eq_top]
    change ((LinearMap.id : Γ(X, V.1) →ₗ[Γ(X, V.1)] Γ(X, V.1)).range :
      Set Γ(X, V.1)) = (⊤ : Ideal Γ(X, V.1))
    simp
  | succ n =>
    have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
    exact ((Modules.ideal_times_quasiCoherent_affine_sections I
      (SheafOfModules.unit X.ringCatSheaf)).2.2.2.1 V).2.2.2 _ (by omega)

set_option backward.isDefEq.respectTransparency false in
private theorem power_product_range {X : Scheme.{u}} (I : X.IdealSheafData)
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) (V : X.affineOpens) :
    LinearMap.range ((idealModuleProductι (idealSheafPower I.toModulesι n).2 M).val.app
      (Opposite.op V.1)).hom = I.ideal V ^ n • (⊤ : Submodule Γ(X, V.1) Γ(M, V.1)) := by
  have := power_qc I n
  apply SetLike.coe_injective
  exact power_range I n V ▸ multiplication_range (idealSheafPower I.toModulesι n).2 M V

set_option backward.isDefEq.respectTransparency false in
private theorem stalk_map_zero_of_over {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (U : X.Opens)
    (hf : (SheafOfModules.overFunctor X.ringCatSheaf U).map f = 0)
    (x : X) (hx : x ∈ U) :
    (RingedSpace.moduleStalkFunctor X.toRingedSpace x).map f = 0 := by
  ext z
  obtain ⟨V, hxV, z, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf z
  have hx' : x ∈ V ⊓ U := ⟨hxV, hx⟩
  rw [← TopCat.Presheaf.germ_res_apply M.presheaf
    (homOfLE inf_le_left : V ⊓ U ⟶ V) x hx' z]
  change (TopCat.Presheaf.stalkFunctor Ab x).map
    ((PresheafOfModules.toPresheaf _).map f.val) _ = 0
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  have h := congrArg (fun q ↦ q.val.app
    (Opposite.op (Over.mk (homOfLE inf_le_right : V ⊓ U ⟶ U)))) hf
  have h' : f.val.app (Opposite.op (V ⊓ U)) = 0 := h
  change TopCat.Presheaf.germ N.presheaf (V ⊓ U) x hx'
    ((f.val.app (Opposite.op (V ⊓ U))).hom (M.presheaf.map (homOfLE inf_le_left).op z)) = 0
  rw [h']
  exact map_zero _

set_option backward.isDefEq.respectTransparency false in
/-- A map that vanishes on the complement vanishes on a sufficiently high ideal-power
submodule. The conclusion is independent of the choice of transition factorization.

Proof: The source I^n G is coherent on a Noetherian scheme. The image Q of χ is
quasi-coherent and finite type on affines (images of finitely many generators suffice),
hence coherent. Its restriction to U is zero, so its support lies in V(I).
The support-power-ideal lemma supplies t with I^t Q = 0. Set m = n+t. On an affine
open W the image of the inclusion of I^m G into G is I(W)^t I(W)^n G(W).
Any factorization r through I^n G is uniquely determined by that inclusion, since the
inclusion of I^n G is mono. By linearity χ sends this submodule into I(W)^t Q(W)=0.
Thus r followed by χ is zero on every affine open, and sheaf separatedness implies
it is zero globally. When U is empty this is the same support-power argument;
when I is the unit ideal the hypothesis already forces χ to vanish.
Source: Stacks Project, Cohomology of Schemes, Lemma 01YB, omitted injectivity,
expanded using Lemma 01Y9 (support-power annihilation).
(blueprint: lem-weil-pbc-coherent-hom-ideal-power-eventually-zero). -/
theorem coherent_hom_ideal_power_eventually_zero {X : Scheme.{u}} [IsLocallyNoetherian X]
    [CompactSpace X] (I : X.IdealSheafData) (F G : X.Modules) [F.IsQuasicoherent]
    (hG : RingedSpace.IsCoherent X.toRingedSpace G) (U : X.Opens)
    (hU : ∀ x : X, x ∈ U ↔ Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map I.toModulesι).hom)
    (n : ℕ) (χ : idealModuleProduct (idealSheafPower I.toModulesι n).2 G ⟶ F)
    (hχ : (SheafOfModules.overFunctor X.ringCatSheaf U).map χ = 0) :
    ∃ (m : ℕ) (_ : n ≤ m),
      ∀ r : idealModuleProduct (idealSheafPower I.toModulesι m).2 G ⟶
          idealModuleProduct (idealSheafPower I.toModulesι n).2 G,
        r ≫ idealModuleProductι (idealSheafPower I.toModulesι n).2 G =
          idealModuleProductι (idealSheafPower I.toModulesι m).2 G → r ≫ χ = 0 := by
  classical
  have : IsNoetherian X := ⟨⟩
  have hGqc := (Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X G).mp hG
  have : G.IsQuasicoherent := hGqc.1
  have := power_qc I n
  let H := idealModuleProduct (idealSheafPower I.toModulesι n).2 G
  let j := idealModuleProductι (idealSheafPower I.toModulesι n).2 G
  have : H.IsQuasicoherent := product_qc _ _
  have hj : Mono j := by dsimp [j, idealModuleProductι]; infer_instance
  have hH := (Modules.isCoherent_kernel_cokernel_biprod_and_submodule X).2
    G H j hG hj inferInstance |>.1
  let Q := Abelian.image χ
  let q := Abelian.factorThruImage χ
  let i := Abelian.image.ι χ
  have him := Modules.quasiCoherent_cokernel_image χ
  have : Q.IsQuasicoherent := him.2.2.2.2.2.2.2.1
  have hfinite (V : X.affineOpens) : Module.Finite Γ(X, V.1) Γ(Q, V.1) := by
    have hfin : Module.Finite Γ(X, V.1) Γ(H, V.1) :=
      Modules.coherent_affine_sections_finite X H hH V.1 V.2
    have hi : Function.Injective (i.app V.1) := (ModuleCat.mono_iff_injective _).mp
      ((SheafOfModules.evaluation _ (Opposite.op V.1)).map_mono i)
    have hs : Function.Surjective (q.app V.1) := by
      intro s
      obtain ⟨z, hz⟩ := (Set.ext_iff.mp (him.2.2.2.2.2.2.2.2 V).1 _).mp ⟨s, rfl⟩
      refine ⟨z, hi ?_⟩
      exact (congrArg (fun f ↦ f.app V.1 z) (Abelian.image.fac χ)).trans hz
    let qL : Γ(H, V.1) →ₗ[Γ(X, V.1)] Γ(Q, V.1) := (q.val.app (Opposite.op V.1)).hom
    exact Module.Finite.of_surjective qL hs
  have hft : Q.IsFiniteType :=
    (((Modules.quasicoherent_finite_type_affine.{u, u} X).2 Q inferInstance).2.1
      X.affineOpens (fun V ↦ V.1) (iSup_affineOpens_eq_top X)
      (fun V ↦ V.2) hfinite).1
  have hQ := (Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X Q).mpr
    ⟨inferInstance, hft⟩
  have hsupp : {x : X | ¬ Subsingleton (Q.presheaf.stalk x)} ⊆
      {x : X | ¬ Function.Surjective
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map I.toModulesι).hom} := by
    intro x hx hi
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
    have hzero : S.map χ = 0 := stalk_map_zero_of_over χ U hχ x ((hU x).mpr hi)
    have hst := (RingedSpace.module_stalk_exact X.toRingedSpace χ).2.2.2.1 x
    have : Epi (S.map q) := hst.1
    have : Mono (S.map i) := hst.2.1
    have hz : S.map i = 0 := by
      apply (cancel_epi (S.map q)).mp
      rw [← S.map_comp, Abelian.image.fac, hzero, comp_zero]
    have hi' := (ModuleCat.mono_iff_injective (S.map i)).mp inferInstance
    apply hx
    refine ⟨fun a b ↦ hi' ?_⟩
    rw [hz]
    rfl
  obtain ⟨t, ht⟩ := (coherent_support_power_ideal_kills X Q hQ I).mpr hsupp
  have hcover : ∀ x : X, ∃ V ∈ (Set.univ : Set X.affineOpens), x ∈ V.1 := by
    intro x
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, _⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨⟨V, hV⟩, Set.mem_univ _, hxV⟩
  have hkill := (idealPowerProduct_isZero_iff_affine_cover X Q I Set.univ hcover t).mp ht
  refine ⟨n + t, Nat.le_add_right n t, ?_⟩
  intro r hr
  apply hom_zero_of_affine
  intro V s
  let L : Γ(H, V.1) →ₗ[Γ(X, V.1)] Γ(G, V.1) := (j.val.app (Opposite.op V.1)).hom
  have hL : Function.Injective L := (ModuleCat.mono_iff_injective _).mp
    ((SheafOfModules.evaluation _ (Opposite.op V.1)).map_mono j)
  have hrange : LinearMap.range L = I.ideal V ^ n • ⊤ :=
    power_product_range I G n V
  have hmem : L (r.app V.1 s) ∈
      (I.ideal V ^ t) • LinearMap.range L := by
    rw [hrange, smul_smul, ← pow_add, Nat.add_comm t n]
    have hs := (power_product_range I G (n + t) V).le
      (show (idealModuleProductι (idealSheafPower I.toModulesι (n + t)).2 G).app V.1 s ∈
        LinearMap.range ((idealModuleProductι
          (idealSheafPower I.toModulesι (n + t)).2 G).val.app (Opposite.op V.1)).hom from ⟨s, rfl⟩)
    have he := congrArg (fun f ↦ f.app V.1 s) hr
    exact he ▸ hs
  rw [← Submodule.map_top L, ← Submodule.map_smul''] at hmem
  obtain ⟨z, hz, he⟩ := hmem
  have he' : z = r.app V.1 s := hL he
  change χ.app V.1 (r.app V.1 s) = 0
  rw [← he']
  refine Submodule.smul_induction_on hz (fun a ha z _ ↦ ?_) (fun a b ha hb ↦ ?_)
  · have hqz := Module.mem_annihilator.mp (hkill V (Set.mem_univ _) ha) (q.app V.1 z)
    have hfac' := congrArg (fun f ↦ f.app V.1 (a • z)) (Abelian.image.fac χ)
    change (i.val.app (Opposite.op V.1)).hom ((q.val.app (Opposite.op V.1)).hom (a • z)) =
      χ.app V.1 (a • z) at hfac'
    change a • (q.val.app (Opposite.op V.1)).hom z = 0 at hqz
    rw [map_smul, hqz, map_zero] at hfac'
    exact hfac'.symm
  · rw [map_add, ha, hb, add_zero]

end AlgebraicGeometry.Scheme
