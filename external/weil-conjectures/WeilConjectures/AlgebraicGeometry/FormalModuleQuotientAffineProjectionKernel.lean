/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

open Scheme.Modules Scheme in
open MonoidalCategory in
set_option backward.isDefEq.respectTransparency false in
private theorem quotient_kernel_product_qc {X : Scheme.{u}} {K : X.Modules}
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

open Scheme.Modules Scheme in
open MonoidalCategory in
open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
private theorem quotient_kernel_multiplication_range {X : Scheme.{u}} {K : X.Modules}
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
/-- The affine formal quotient projection has kernel I^m M.
Source: Stacks Project, Tags 01I8, 01IC and 087W, affine module correspondence.
(blueprint: lem-weil-pbc-formal-module-quotient-affine-projection-ker).

Proof: Write F for the associated sheaf of M and U for the whole spectrum.
The ideal-times affine-sections theorem gives quasi-coherence of the positive
power K and identifies the range of its inclusion with J(U)^m. The product K F
is the image of the multiplication K tensor F to F. The affine tensor comparison
sends a pure tensor to the scalar multiple of its second factor by the image of
its first factor. Tensor induction shows that this multiplication has range
J(U)^m times all sections of F; conversely every generator of that submodule is
such a pure tensor image. The affine image theorem identifies this range with
the range of the product inclusion. Quasi-coherence of the tensor product, its
cokernel and its kernel gives quasi-coherence of K F. The affine cokernel-image
theorem applied to its inclusion says that the kernel of the quotient projection
is this range. The assumption hJ identifies J(U) with I mapped along the inverse
of GammaSpecIso; mapping commutes with ideal powers. The tilde unit identifies
M with the sections of F after restricting scalars along that same isomorphism.
Its linearity transports each generator r times x of I^m M to the corresponding
generator of J(U)^m F(U), and its inverse transports generators back. Thus the
inverse image of the sectionwise kernel is exactly I^m M. This is the asserted
kernel of p. For I=0 the kernel is zero, for I=top it is all of M, and M=0 is
immediate; no finiteness or completeness condition is used. -/
theorem formalModuleQuotient_affine_projection_kernel
    (A : Type u) [CommRing A] (I : Ideal A)
    (J : (Spec (CommRingCat.of A)).IdealSheafData)
    (hJ : J = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
    (M : ModuleCat.{u} A) (m : ℕ) (hm : 0 < m) :
    let p := (tilde.toTildeΓNatIso (R := CommRingCat.of A)).hom.app M ≫
      (moduleSpecΓFunctor (R := CommRingCat.of A)).map
        (formalModuleQuotientπ J m ((tilde.functor (CommRingCat.of A)).obj M))
    LinearMap.ker p.hom = I ^ m • (⊤ : Submodule A M) := by
  let F := (tilde.functor (CommRingCat.of A)).obj M
  let U : (Spec (CommRingCat.of A)).affineOpens :=
    ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of A))⟩
  have : F.IsQuasicoherent := by
    change (tilde.{u} (R := CommRingCat.of A) M).IsQuasicoherent
    infer_instance
  have ht := Scheme.Modules.ideal_times_quasiCoherent_affine_sections J F
  have := ht.2.2.1 m hm
  have := quotient_kernel_product_qc (Scheme.idealSheafPower J.toModulesι m).2 F
  have hr := quotient_kernel_multiplication_range
    (Scheme.idealSheafPower J.toModulesι m).2 F U
  have hpow : (LinearMap.range
      ((Scheme.idealSheafPower J.toModulesι m).2.val.app (op U.1)).hom :
        Ideal Γ(Spec (CommRingCat.of A), U.1)) = J.ideal U ^ m := by
    apply SetLike.coe_injective
    exact (ht.2.2.2.1 U).2.2.2 m hm
  dsimp only at hr
  rw [hpow] at hr
  have hk := (Scheme.Modules.quasiCoherent_cokernel_image
    (Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι m).2 F)).2.2.2.2.2.2.2.2 U
  have hj : J.ideal U ^ m =
      (I ^ m).map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom := by
    rw [hJ, Scheme.IdealSheafData.ideal_top_ofIdealTop, Ideal.map_pow]
  rw [hj] at hr
  let e := (tilde.toTildeΓNatIso (R := CommRingCat.of A)).app M
  ext x
  change (formalModuleQuotientπ J m F).app U.1 (e.hom x) = 0 ↔ _
  have hx : (formalModuleQuotientπ J m F).app U.1 (e.hom x) = 0 ↔
      e.hom x ∈ ((I ^ m).map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) •
        (⊤ : Submodule Γ(Spec (CommRingCat.of A), U.1) Γ(F, U.1)) := by
    change e.hom x ∈ LinearMap.ker
      ((cokernel.π (Scheme.idealModuleProductι
        (Scheme.idealSheafPower J.toModulesι m).2 F)).val.app (op U.1)).hom ↔ _
    rw [hk.2.2.1]
    exact Set.ext_iff.mp hr (e.hom x)
  rw [hx]
  constructor
  · intro hx
    have hh : ∀ (y : Γ(F, U.1)),
        y ∈ ((I ^ m).map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) •
          (⊤ : Submodule Γ(Spec (CommRingCat.of A), U.1) Γ(F, U.1)) →
        e.inv y ∈ I ^ m • (⊤ : Submodule A M) := by
      intro y hy
      refine Submodule.smul_induction_on hy (fun r hr y _ ↦ ?_) (fun y z hy hz ↦ ?_)
      · obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective _
          (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv.surjective).mp hr
        change e.inv (a • (show (moduleSpecΓFunctor (R := CommRingCat.of A)).obj F from y)) ∈ _
        rw [_root_.map_smul]
        exact Submodule.smul_mem_smul ha (Submodule.mem_top)
      · rw [map_add]
        exact Submodule.add_mem _ hy hz
    simpa using hh (e.hom x) hx
  · intro hx
    have hh : ∀ (y : M), y ∈ I ^ m • (⊤ : Submodule A M) →
        e.hom y ∈ ((I ^ m).map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) •
          (⊤ : Submodule Γ(Spec (CommRingCat.of A), U.1) Γ(F, U.1)) := by
      intro y hy
      refine Submodule.smul_induction_on hy (fun r hr y _ ↦ ?_) (fun y z hy hz ↦ ?_)
      · rw [_root_.map_smul]
        change (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom r •
          (show Γ(F, U.1) from e.hom y) ∈ _
        exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) (Submodule.mem_top)
      · rw [map_add]
        exact Submodule.add_mem _ hy hz
    exact hh x hx

end AlgebraicGeometry
