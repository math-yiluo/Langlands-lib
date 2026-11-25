/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel

/-! # Image of multiplication restricted to an ideal multiple of a tensor product

Source: Stacks Project, Tag 01YB, last displayed map in the proof.
(blueprint: lem-pc-ideal-tensor-restricted-multiplication-image)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

open MonoidalCategory in
open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
open Opposite in
/-- Affine ranges of ideal products after an arbitrary module morphism. -/
private theorem restricted_product_affine {X : Scheme.{u}} {K N : X.Modules}
    (i : K ⟶ SheafOfModules.unit X.ringCatSheaf) (M : X.Modules) (φ : M ⟶ N)
    [K.IsQuasicoherent] [M.IsQuasicoherent] :
    (idealModuleProduct i M).IsQuasicoherent ∧ ∀ U : X.affineOpens,
      LinearMap.range ((idealModuleProductι i M ≫ φ).val.app (op U.1)).hom =
        (LinearMap.range (i.val.app (op U.1)).hom : Ideal Γ(X, U.1)) •
          (LinearMap.range (φ.val.app (op U.1)).hom :
            Submodule Γ(X, U.1) Γ(N, U.1)) := by
  constructor
  · let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    have := (quasiCoherent_tensor_product_affine_sections K M).1
    let a := i ▷ M ≫ (λ_ M).hom
    have := isQuasicoherent_cokernel a
    have := isQuasicoherent_kernel (cokernel.π a)
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (Abelian.imageIsoImage a) inferInstance
  · intro U
    have hm : Set.range ((idealModuleProductι i M).app U.1) =
        {s | s ∈ (LinearMap.range (i.val.app (op U.1)).hom : Ideal Γ(X, U.1)) •
          (⊤ : Submodule Γ(X, U.1) Γ(M, U.1))} := by
      let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
      let a := i ▷ M ≫ (λ_ M).hom
      have := (quasiCoherent_tensor_product_affine_sections K M).1
      have ht := (quasiCoherent_tensor_product_affine_sections K M).2 U.1 U.2
      let I : Ideal Γ(X, U.1) := LinearMap.range (i.val.app (op U.1)).hom
      have hp (s : Γ(K, U.1)) (t : Γ(M, U.1)) :
          a.app U.1 (tensorSectionsMap K M U.1 (s ⊗ₜ t)) =
            (show Γ(X, U.1) from i.app U.1 s) • t := by
        rw [tensorSectionsMap_tmul]
        change (λ_ M).hom.app U.1 ((i ▷ M).app U.1 (tmulSection s t)) = _
        rw [whiskerRight_app_tmulSection, leftUnitor_hom_app_tmulSection']
        rfl
      have ha : LinearMap.range (a.val.app (op U.1)).hom =
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
    have hm' : LinearMap.range ((idealModuleProductι i M).val.app (op U.1)).hom =
        (LinearMap.range (i.val.app (op U.1)).hom : Ideal Γ(X, U.1)) •
          (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)) := SetLike.coe_injective hm
    change LinearMap.range ((φ.val.app (op U.1)).hom.comp
      ((idealModuleProductι i M).val.app (op U.1)).hom) = _
    rw [LinearMap.range_comp, hm', Submodule.map_smul'', Submodule.map_top]


set_option backward.isDefEq.respectTransparency false in
open Opposite in
/-- All powers of an arbitrary quasi-coherent ideal inclusion, including power zero. -/
private theorem restricted_powers_affine {X : Scheme.{u}} {K : X.Modules}
    (i : K ⟶ SheafOfModules.unit X.ringCatSheaf) [K.IsQuasicoherent] (n : ℕ) :
    (idealSheafPower i n).1.IsQuasicoherent ∧ ∀ U : X.affineOpens,
      (LinearMap.range ((idealSheafPower i n).2.val.app (op U.1)).hom :
        Ideal Γ(X, U.1)) = (LinearMap.range (i.val.app (op U.1)).hom : Ideal Γ(X, U.1)) ^ n
        := by
  have hqc (n : ℕ) : (idealSheafPower i n).1.IsQuasicoherent := by
    induction n using Nat.twoStepInduction with
    | zero => exact SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
    | one => assumption
    | more n _ ih => exact (restricted_product_affine i _ (𝟙 _)).1
  refine ⟨hqc n, ?_⟩
  intro U
  induction n with
  | zero =>
    change LinearMap.range (LinearMap.id : Γ(X, U.1) →ₗ[Γ(X, U.1)] Γ(X, U.1)) = _
    simp
  | succ n ih =>
    cases n with
    | zero => simp [idealSheafPower]
    | succ n =>
      have := hqc (n + 1)
      change LinearMap.range
        (((idealSheafPower i (n + 1)).2.val.app (op U.1)).hom.comp
          ((idealModuleProductι i
            (idealSheafPower i (n + 1)).1).val.app (op U.1)).hom) = _
      have hp := (restricted_product_affine i (idealSheafPower i (n + 1)).1 (𝟙 _)).2 U
      change LinearMap.range
        ((idealModuleProductι i (idealSheafPower i (n + 1)).1).val.app (op U.1)).hom =
        (LinearMap.range (i.val.app (op U.1)).hom : Ideal Γ(X, U.1)) •
          LinearMap.range (LinearMap.id : Γ((idealSheafPower i (n + 1)).1, U.1) →ₗ[Γ(X, U.1)]
            Γ((idealSheafPower i (n + 1)).1, U.1)) at hp
      rw [LinearMap.range_id] at hp
      rw [LinearMap.range_comp, hp, Submodule.map_smul'', Submodule.map_top, ih,
        Ideal.smul_eq_mul]
      exact (pow_succ'
        (LinearMap.range (i.val.app (op U.1)).hom : Ideal Γ(X, U.1)) (n + 1)).symm

open Opposite in
/-- Transfer the affine range formula to any isomorphic image presentation.
Source: Stacks Project, proof of Lemma 01YP
(blueprint: lem-weil-pbc-closed-immersion-ideal-power-image). -/
private theorem restricted_image_range_affine {X : Scheme.{u}} {M N P : X.Modules}
    (φ : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (j : P ⟶ N) (e₀ : P ≅ image φ) (hj : e₀.hom ≫ image.ι φ = j)
    (U : X.affineOpens) :
    Set.range (j.app U.1) = Set.range (φ.app U.1) := by
  have h₀ : Set.range (j.app U.1) = Set.range ((image.ι φ).app U.1) := by
    rw [← hj, Modules.Hom.comp_app]
    exact (Modules.appLinearEquivOfIso e₀ U.1).surjective.range_comp _
  rw [h₀]
  let e := Abelian.imageIsoImage φ
  have he : Function.Surjective (e.hom.app U.1) :=
    (Modules.appLinearEquivOfIso e U.1).surjective
  have hf : e.hom ≫ image.ι φ = Abelian.image.ι φ :=
    Abelian.imageIsoImage_hom_comp_image_ι φ
  have hr : Set.range ((image.ι φ).app U.1) =
      Set.range ((Abelian.image.ι φ).app U.1) := by
    rw [← hf, Modules.Hom.comp_app]
    ext s
    constructor
    · rintro ⟨t, rfl⟩
      obtain ⟨a, rfl⟩ := he t
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨e.hom.app U.1 a, rfl⟩
  exact hr.trans ((Modules.quasiCoherent_cokernel_image φ).2.2.2.2.2.2.2.2 U).1

open Opposite in
/-- Sheaf separatedness detects a zero morphism on any topological basis.
Source: Stacks Project, proof of Lemma 01YP
(blueprint: lem-weil-pbc-closed-immersion-ideal-power-image). -/
private theorem restricted_hom_zero_of_basis {X : Scheme.{u}} {M N : X.Modules}
    (B : Set X.Opens) (hB : TopologicalSpace.IsTopologicalBasis
      ((fun V : X.Opens ↦ (V : Set X)) '' B))
    (φ : M ⟶ N) (h : ∀ V : B, ∀ s : Γ(M, V.1), φ.app V.1 s = 0) :
    φ = 0 := by
  apply Modules.hom_ext
  intro W
  ext s
  change φ.app W s = 0
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩
    (fun i : {V : B // V.1 ≤ W} ↦ i.1.1) W
    (fun i ↦ homOfLE i.2) ?_ _ _ ?_
  · intro x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
      hB.exists_subset_of_mem_open hx W.2
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVW⟩, hxV⟩
  · intro i
    rw [← Modules.Hom.app_presheaf_map, map_zero]
    exact h i.1 _

open Opposite in
/-- Factor an inclusion through a monomorphism by vanishing of its cokernel projection.
Source: Stacks Project, proof of Lemma 01YP
(blueprint: lem-weil-pbc-closed-immersion-ideal-power-image). -/
private theorem restricted_subobject_le_of_basis_range {X : Scheme.{u}} {M N P : X.Modules}
    (B : Set X.Opens) (hB : TopologicalSpace.IsTopologicalBasis
      ((fun V : X.Opens ↦ (V : Set X)) '' B))
    (i : M ⟶ P) (j : N ⟶ P) [Mono i] [Mono j]
    (h : ∀ V : B, Set.range (i.app V.1) ⊆ Set.range (j.app V.1)) :
    Subobject.mk i ≤ Subobject.mk j := by
  have hz : i ≫ cokernel.π j = 0 := by
    apply restricted_hom_zero_of_basis B hB
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

set_option backward.isDefEq.respectTransparency false in
/-- The image of I^m times tensor multiplication is the higher ideal product.
Source: Stacks Project, Tag 01YB, last displayed map; affine product and tensor
comparisons in Tags 01I8 and 01AH.
(blueprint: lem-pc-ideal-tensor-restricted-multiplication-image)

Proof: Put T = I^n tensor H and let μ be multiplication. On each affine open U,
the tensor comparison identifies its sections with I(U)^n tensor H(U).
The recursive ideal power at m has inclusion range I(U)^m, also for m=0.
The affine product theorem gives the inclusion range I(U)^m T(U). Multiplication
maps this onto I(U)^m I(U)^n H(U) = I(U)^(n+m) H(U): one inclusion follows from
linearity, the reverse from writing ideal products as sums of products and lifting
each pure product to a tensor. The affine image theorem identifies the image of
the composite with this range. The ideal-sheaf-data product at n+m has the same
range. Both inclusions are monomorphisms. Equality of ranges on the affine basis
gives inverse factorizations between the subsheaves, since the unique local
preimages agree on overlaps and glue. These give e, with the required inclusion
identity. No Noetherianity or finiteness is needed. At either exponent zero the
same affine formula uses the unit ideal; zero ideals and zero H give zero images. -/
theorem ideal_tensor_restricted_multiplication_image
    {X : Scheme.{u}} (I : X.IdealSheafData) (H : X.Modules)
    [H.IsQuasicoherent] (n m : ℕ) :
    letI : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    let T := (I ^ n).toModules ⊗ H
    let μ := (I ^ n).toModulesι ▷ H ≫ (λ_ H).hom
    let j := idealModuleProductι (idealSheafPower I.toModulesι m).2 T
    ∃ e : idealModuleProduct (I ^ (n + m)).toModulesι H ≅ image (j ≫ μ),
      e.hom ≫ image.ι (j ≫ μ) = idealModuleProductι (I ^ (n + m)).toModulesι H := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  let T := (I ^ n).toModules ⊗ H
  let μ : T ⟶ H := (I ^ n).toModulesι ▷ H ≫ (λ_ H).hom
  let j := idealModuleProductι (idealSheafPower I.toModulesι m).2 T
  let k := idealModuleProductι (I ^ (n + m)).toModulesι H
  have hIq (J : X.IdealSheafData) : J.toModules.IsQuasicoherent := by
    have := SheafOfModules.isQuasicoherent_unit (R := J.subscheme.ringCatSheaf)
    have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
    have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf)
        ((SheafOfModules.pushforward J.subschemeι.toRingCatSheafHom).obj
          (SheafOfModules.unit J.subscheme.ringCatSheaf)) :=
      by
        let f := J.subschemeι
        let F := SheafOfModules.unit J.subscheme.ringCatSheaf
        refine isQuasicoherent_of_forall_isAffineOpen _ (fun W hW g s ↦ ?_) (fun W hW g t ht ↦ ?_)
        · obtain ⟨n, t, ht⟩ := exists_map_eq_pow_smul_of_basicOpen_eq F
            (IsAffineOpen.preimage (U := W) hW f) (f.app W g)
            (f.preimage_basicOpen g).symm (f.preimage_mono (X.basicOpen_le g)) s
          refine ⟨n, t, ht.trans ?_⟩
          have h : f.app (X.basicOpen g) (X.presheaf.map (homOfLE (X.basicOpen_le g)).op g) =
              J.subscheme.presheaf.map (homOfLE (f.preimage_mono (X.basicOpen_le g))).op
                (f.app W g) := by
            rw [← ConcreteCategory.comp_apply, f.naturality]
            rfl
          rw [← h, ← map_pow]
          rfl
        · obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_basicOpen_eq F
            (IsAffineOpen.preimage (U := W) hW f) (f.app W g)
            (f.preimage_basicOpen g).symm (f.preimage_mono (X.basicOpen_le g)) t ht
          rw [← map_pow] at hn
          exact ⟨n, hn⟩
    exact isQuasicoherent_kernel J.toPushforwardSubscheme
  have := hIq (I ^ n)
  have := (quasiCoherent_tensor_product_affine_sections (I ^ n).toModules H).1
  have := hIq I
  have := (restricted_powers_affine I.toModulesι m).1
  have := (restricted_product_affine (idealSheafPower I.toModulesι m).2 T (𝟙 _)).1
  have : Mono k := by dsimp [k, idealModuleProductι]; infer_instance
  have hr (U : X.affineOpens) :
      Set.range ((image.ι (j ≫ μ)).app U.1) = Set.range (k.app U.1) := by
    rw [restricted_image_range_affine (j ≫ μ) _ (Iso.refl _) (by simp) U]
    have hpow : (LinearMap.range
        ((idealSheafPower I.toModulesι m).2.val.app (Opposite.op U.1)).hom :
          Ideal Γ(X, U.1)) = I.ideal U ^ m := by
      have hI : (LinearMap.range (I.toModulesι.val.app (Opposite.op U.1)).hom :
          Ideal Γ(X, U.1)) = I.ideal U :=
        SetLike.coe_injective (I.range_toModulesι_app U)
      exact hI ▸ (restricted_powers_affine I.toModulesι m).2 U
    have hcomp : LinearMap.range ((j ≫ μ).val.app (Opposite.op U.1)).hom =
        I.ideal U ^ m • (LinearMap.range (μ.val.app (Opposite.op U.1)).hom :
          Submodule Γ(X, U.1) Γ(H, U.1)) := by
      have hp := (restricted_product_affine (idealSheafPower I.toModulesι m).2 T μ).2 U
      simpa only [hpow] using hp
    have hprod (J : X.IdealSheafData) :
        LinearMap.range ((idealModuleProductι J.toModulesι H).val.app
          (Opposite.op U.1)).hom =
          J.ideal U • (⊤ : Submodule Γ(X, U.1) Γ(H, U.1)) := by
      have := hIq J
      have hI : (LinearMap.range (J.toModulesι.val.app (Opposite.op U.1)).hom :
          Ideal Γ(X, U.1)) = J.ideal U :=
        SetLike.coe_injective (J.range_toModulesι_app U)
      have hp := (restricted_product_affine J.toModulesι H (𝟙 _)).2 U
      change LinearMap.range ((idealModuleProductι J.toModulesι H).val.app
          (Opposite.op U.1)).hom =
        (LinearMap.range (J.toModulesι.val.app (Opposite.op U.1)).hom : Ideal Γ(X, U.1)) •
          LinearMap.range (LinearMap.id : Γ(H, U.1) →ₗ[Γ(X, U.1)] Γ(H, U.1)) at hp
      simpa only [LinearMap.range_id, hI] using hp
    have hμ : LinearMap.range (μ.val.app (Opposite.op U.1)).hom =
        I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) Γ(H, U.1)) := by
      apply SetLike.coe_injective
      exact (restricted_image_range_affine μ _ (Iso.refl _) (by rfl) U).symm.trans
        (congrArg (fun P : Submodule Γ(X, U.1) Γ(H, U.1) ↦ (P : Set Γ(H, U.1)))
          (hprod (I ^ n)))
    have hk : LinearMap.range (k.val.app (Opposite.op U.1)).hom =
        I.ideal U ^ (n + m) • (⊤ : Submodule Γ(X, U.1) Γ(H, U.1)) := by
      exact hprod (I ^ (n + m))
    have hh : LinearMap.range ((j ≫ μ).val.app (Opposite.op U.1)).hom =
        LinearMap.range (k.val.app (Opposite.op U.1)).hom := by
      rw [hcomp, hμ, hk, ← Submodule.mul_smul, ← pow_add, Nat.add_comm m n]
    exact congrArg (fun P : Submodule Γ(X, U.1) Γ(H, U.1) ↦ (P : Set Γ(H, U.1))) hh
  have hs : Subobject.mk k = Subobject.mk (image.ι (j ≫ μ)) :=
    le_antisymm
      (restricted_subobject_le_of_basis_range _ X.isBasis_affineOpens k _ (fun U ↦ (hr U).ge))
      (restricted_subobject_le_of_basis_range _ X.isBasis_affineOpens _ k (fun U ↦ (hr U).le))
  refine ⟨Subobject.isoOfMkEqMk _ _ hs, ?_⟩
  exact Subobject.ofMkLEMk_comp hs.le

end AlgebraicGeometry.Scheme.Modules
