/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.RingTheory.Ideal.Operations
import Mathlib.CategoryTheory.Subobject.Limits
import WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.AlgebraicGeometry.Cohomology.Restriction

/-!
# Products of quasi-coherent ideals and modules

A quasi-coherent ideal is a `Scheme.IdealSheafData`, with module realization and inclusion
`toModules` and `toModulesι`. The product `𝒥𝓕`, its inclusion and the powers `𝒥ⁿ`
(`𝒥ⁿ⁺¹ = 𝒥 · 𝒥ⁿ`) are `Scheme.idealModuleProduct`, `Scheme.idealModuleProductι`
and `Scheme.idealSheafPower`. Restriction to an
open `V` is `Scheme.Modules.restrictFunctor V.ι` on modules and `IdealSheafData.comap V.ι`
on ideals. Subsheaves of `𝓕|_V` are compared as the subobjects `Subobject.mk (image.ι _)`
of their inclusions.

## References

* Stacks Project, Schemes, Tags 01I8 and 01IC
* Stacks Project, Modules, Tags 01CE and 01AH
* Stacks Project, Cohomology of Schemes, Tag 087X
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules


private theorem ideal_qc {X : Scheme.{u}} (J : X.IdealSheafData) :
    J.toModules.IsQuasicoherent := by
  have := SheafOfModules.isQuasicoherent_unit (R := J.subscheme.ringCatSheaf)
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf)
      ((SheafOfModules.pushforward J.subschemeι.toRingCatSheafHom).obj
        (SheafOfModules.unit J.subscheme.ringCatSheaf)) :=
    isQuasicoherent_pushforward_of_isClosedImmersion J.subschemeι _
  exact isQuasicoherent_kernel J.toPushforwardSubscheme

open MonoidalCategory in
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

open MonoidalCategory in
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


set_option backward.isDefEq.respectTransparency false in
private theorem product_range {X : Scheme.{u}} (J : X.IdealSheafData)
    (M : X.Modules) [M.IsQuasicoherent] (U : X.affineOpens) :
    LinearMap.range ((idealModuleProductι J.toModulesι M).val.app (op U.1)).hom =
      J.ideal U • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)) := by
  have := ideal_qc J
  have hI : (LinearMap.range (J.toModulesι.val.app (op U.1)).hom : Ideal Γ(X, U.1)) =
      J.ideal U := SetLike.coe_injective (J.range_toModulesι_app U)
  apply SetLike.coe_injective
  exact hI ▸ multiplication_range J.toModulesι M U

set_option backward.isDefEq.respectTransparency false in
private theorem powers_qc {X : Scheme.{u}} {K : X.Modules}
    (i : K ⟶ SheafOfModules.unit X.ringCatSheaf) [K.IsQuasicoherent] (n : ℕ) :
    (idealSheafPower i n).1.IsQuasicoherent := by
  induction n using Nat.twoStepInduction with
  | zero =>
    exact SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  | one => assumption
  | more n _ ih => exact product_qc i _

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
    have := ideal_qc J
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

set_option backward.isDefEq.respectTransparency false in
private theorem restriction_range {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (J : X.IdealSheafData) (F : X.Modules)
    [F.IsQuasicoherent] (V : Y.affineOpens) :
    Set.range (((restrictFunctor j).map (idealModuleProductι J.toModulesι F)).app V.1) =
      Set.range ((idealModuleProductι (J.comap j).toModulesι (F.restrict j)).app V.1) := by
  let U : X.affineOpens := ⟨j ''ᵁ V.1, V.2.image_of_isOpenImmersion j⟩
  have := isQuasicoherent_restrictFunctor j F
  have hI : (J.comap j).ideal V = Ideal.map (j.appIso V.1).hom.hom (J.ideal U) := by
    rw [Scheme.Hom.appIso_hom']
    exact J.ideal_comap_appLE j U V (j.preimage_image_eq V.1).ge
  have hR := product_range J F U
  have hL := product_range (J.comap j) (F.restrict j) V
  have hR' : Set.range
      (((restrictFunctor j).map (idealModuleProductι J.toModulesι F)).app V.1) =
      {s : Γ(F, U.1) | s ∈ J.ideal U • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1))} :=
    congrArg (fun P : Submodule Γ(X, U.1) Γ(F, U.1) ↦ (P : Set Γ(F, U.1))) hR
  rw [hR']
  have hL' : Set.range
      ((idealModuleProductι (J.comap j).toModulesι (F.restrict j)).app V.1) =
      {s | s ∈ (J.comap j).ideal V •
        (⊤ : Submodule Γ(Y, V.1) Γ(F.restrict j, V.1))} :=
    congrArg (fun P : Submodule Γ(Y, V.1) Γ(F.restrict j, V.1) ↦
      (P : Set Γ(F.restrict j, V.1))) hL
  rw [hL', hI]
  ext (s : Γ(F.restrict j, V.1))
  change (F.restrictAppIso j V.1).hom s ∈
    J.ideal U • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1)) ↔
      s ∈ Ideal.map (j.appIso V.1).hom.hom (J.ideal U) •
        (⊤ : Submodule Γ(Y, V.1) Γ(F.restrict j, V.1))
  constructor
  · intro hs
    have h (t : Γ(F, U.1))
        (ht : t ∈ J.ideal U • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1))) :
        (F.restrictAppIso j V.1).inv t ∈
          Ideal.map (j.appIso V.1).hom.hom (J.ideal U) •
            (⊤ : Submodule Γ(Y, V.1) Γ(F.restrict j, V.1)) := by
      refine Submodule.smul_induction_on ht (fun r hr t _ ↦ ?_) (fun a b ha hb ↦ ?_)
      · rw [smul_restrictAppIso_inv_apply]
        exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) (Submodule.mem_top)
      · rw [map_add]
        exact Submodule.add_mem _ ha hb
    exact h _ hs
  · intro hs
    refine Submodule.smul_induction_on hs (fun r hr t _ ↦ ?_) (fun a b ha hb ↦ ?_)
    · obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective
        (j.appIso V.1).hom.hom (j.appIso V.1).commRingCatIsoToRingEquiv.surjective).mp hr
      rw [smul_restrictAppIso_hom_apply]
      have he : (j.appIso V.1).inv ((j.appIso V.1).hom a) = a :=
        (j.appIso V.1).commRingCatIsoToRingEquiv.symm_apply_apply a
      rw [he]
      exact Submodule.smul_mem_smul ha (Submodule.mem_top)
    · rw [map_add]
      exact Submodule.add_mem _ ha hb

/-- Products and quotients by quasi-coherent ideals, including affine sections and
restriction to arbitrary opens. Let `𝒥` be a quasi-coherent ideal and `𝓕` a quasi-coherent
module on `X`. Then `𝒥𝓕`, `𝓕/𝒥𝓕` and every `𝒥ⁿ` (`n ≥ 1`) are quasi-coherent; on every
affine open `U`, `(𝒥𝓕)(U) = 𝒥(U)𝓕(U)`, `𝓕(U) → (𝓕/𝒥𝓕)(U)` is surjective with kernel
`𝒥(U)𝓕(U)`, and `𝒥ⁿ(U) = 𝒥(U)ⁿ`; for every open `V`, `(𝒥𝓕)|_V = (𝒥|_V)(𝓕|_V)` as
subobjects of `𝓕|_V`. -/
theorem ideal_times_quasiCoherent_affine_sections {X : Scheme.{u}}
    (J : X.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent] :
    (idealModuleProduct J.toModulesι F).IsQuasicoherent ∧
    (cokernel (idealModuleProductι J.toModulesι F)).IsQuasicoherent ∧
    (∀ n : ℕ, 0 < n → (idealSheafPower J.toModulesι n).1.IsQuasicoherent) ∧
    (∀ U : X.affineOpens,
      Set.range ((idealModuleProductι J.toModulesι F).app U.1) =
        {s | s ∈ J.ideal U • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1))} ∧
      Function.Surjective ((cokernel.π (idealModuleProductι J.toModulesι F)).app U.1) ∧
      (∀ s : Γ(F, U.1),
        (cokernel.π (idealModuleProductι J.toModulesι F)).app U.1 s = 0 ↔
          s ∈ J.ideal U • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1))) ∧
      (∀ n : ℕ, 0 < n →
        Set.range ((idealSheafPower J.toModulesι n).2.app U.1) =
          {a | a ∈ J.ideal U ^ n})) ∧
    (∀ V : X.Opens,
      Subobject.mk (image.ι ((restrictFunctor V.ι).map (idealModuleProductι J.toModulesι F))) =
        Subobject.mk (image.ι (idealModuleProductι (J.comap V.ι).toModulesι
          ((restrictFunctor V.ι).obj F)))) := by
  have := ideal_qc J
  have hprod := product_qc J.toModulesι F
  have := hprod
  refine ⟨hprod, isQuasicoherent_cokernel _, fun n _ ↦ powers_qc J.toModulesι n, ?_, ?_⟩
  · intro U
    have hr := product_range J F U
    have hq := (quasiCoherent_cokernel_image
      (idealModuleProductι J.toModulesι F)).2.2.2.2.2.2.2.2 U
    refine ⟨congrArg (fun P : Submodule Γ(X, U.1) Γ(F, U.1) ↦
      (P : Set Γ(F, U.1))) hr, hq.2.1, ?_, ?_⟩
    · intro s
      change s ∈ LinearMap.ker
        ((cokernel.π (idealModuleProductι J.toModulesι F)).val.app (op U.1)).hom ↔ _
      rw [hq.2.2.1, hr]
    · intro n hn
      exact congrArg (fun I : Ideal Γ(X, U.1) ↦ (I : Set Γ(X, U.1)))
        (powers_range J U n hn)
  · intro V
    have hom_zero_of_affine : ∀ {X : Scheme.{u}} {M N : X.Modules}
        (φ : M ⟶ N), (∀ V : X.affineOpens, ∀ s : Γ(M, V.1), φ.app V.1 s = 0) → φ = 0 := by
      intro X M N φ h
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
        rw [← Hom.app_presheaf_map, map_zero]
        exact h i.1 _
    have subobject_le_of_affine_range : ∀ {X : Scheme.{u}} {M N P : X.Modules}
        (i : M ⟶ P) (j : N ⟶ P) [Mono i] [Mono j],
        (∀ V : X.affineOpens, Set.range (i.app V.1) ⊆ Set.range (j.app V.1)) →
          Subobject.mk i ≤ Subobject.mk j := by
      intro X M N P i j _ _ h
      have hz : i ≫ cokernel.π j = 0 := by
        apply hom_zero_of_affine
        intro V s
        obtain ⟨t, ht⟩ := h V ⟨s, rfl⟩
        change (cokernel.π j).app V.1 (i.app V.1 s) = 0
        rw [← ht]
        exact congrArg (fun q ↦ q.app V.1 t) (cokernel.condition j)
      let k : M ⟶ Abelian.image j := kernel.lift (cokernel.π j) i hz
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
        _ = i := kernel.lift_ι _ _ hz
    let i := (restrictFunctor V.ι).map (idealModuleProductι J.toModulesι F)
    let k := idealModuleProductι (J.comap V.ι).toModulesι (F.restrict V.ι)
    have : Mono (idealModuleProductι J.toModulesι F) := by
      dsimp [idealModuleProductι]
      infer_instance
    have : Mono i := by
      dsimp [i]
      exact Functor.map_mono (restrictFunctor V.ι) _
    have : Mono k := by dsimp [k, idealModuleProductι]; infer_instance
    change imageSubobject i = imageSubobject k
    rw [imageSubobject_mono, imageSubobject_mono]
    apply le_antisymm
    · exact subobject_le_of_affine_range i k
        (fun U ↦ (restriction_range V.ι J F U).subset)
    · exact subobject_le_of_affine_range k i
        (fun U ↦ (restriction_range V.ι J F U).symm.subset)

end AlgebraicGeometry.Scheme.Modules
