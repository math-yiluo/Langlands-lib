/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.AlgebraicGeometry.IdealPowerProductZeroAffineCover
import WeilConjectures.RingTheory.KernelCokernelAnnihilatedModIdeal
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
/-! Kernel half of reduction torsion. -/
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
open MonoidalCategory in
open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
/-- Affine sections of multiplication have range equal to the ideal times the module.
Source: Stacks Project, Tags 01I8 and 01AH
(blueprint: lem-weil-pbc-ideal-times-quasi-coherent-affine-sections).
Proof: the affine tensor comparison is surjective and multiplication sends a pure tensor
to its scalar multiple. Tensor induction gives one range inclusion; pure tensors give
the other. The affine image theorem and the canonical image isomorphism identify this
range with that of the product inclusion. The matching upstream helper is private. -/
private theorem power_multiplication_range {X : Scheme.{u}} {K : X.Modules}
    (i : K ⟶ SheafOfModules.unit X.ringCatSheaf) (M : X.Modules)
    [K.IsQuasicoherent] [M.IsQuasicoherent] (U : X.affineOpens) :
    let I : Ideal Γ(X, U.1) := LinearMap.range (i.val.app (op U.1)).hom
    Set.range ((Scheme.idealModuleProductι i M).app U.1) =
      {s | s ∈ I • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1))} := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  let a := i ▷ M ≫ (λ_ M).hom
  have := (Scheme.Modules.quasiCoherent_tensor_product_affine_sections K M).1
  have ht := (Scheme.Modules.quasiCoherent_tensor_product_affine_sections K M).2 U.1 U.2
  let I : Ideal Γ(X, U.1) := LinearMap.range (i.val.app (op U.1)).hom
  have hp (s : Γ(K, U.1)) (t : Γ(M, U.1)) :
      a.app U.1 (Scheme.Modules.tensorSectionsMap K M U.1 (s ⊗ₜ t)) =
        (show Γ(X, U.1) from i.app U.1 s) • t := by
    rw [Scheme.Modules.tensorSectionsMap_tmul]
    change (λ_ M).hom.app U.1 ((i ▷ M).app U.1 (Scheme.Modules.tmulSection s t)) = _
    rw [Scheme.Modules.whiskerRight_app_tmulSection, Scheme.Modules.leftUnitor_hom_app_tmulSection']
    rfl
  have ha : LinearMap.range (a.val.app (op U.1)).hom = I • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)) := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      obtain ⟨w, rfl⟩ := ht.2 z
      induction w using TensorProduct.inductionOn with
      | tmul s t =>
        change a.app U.1 (Scheme.Modules.tensorSectionsMap K M U.1 (s ⊗ₜ t)) ∈ I • ⊤
        rw [hp]
        exact Submodule.smul_mem_smul ⟨s, rfl⟩ (Submodule.mem_top)
      | add x y hx hy =>
        simp only [map_add]
        exact Submodule.add_mem _ hx hy
    · apply Submodule.smul_le.mpr
      intro r hr t _
      obtain ⟨s, rfl⟩ := hr
      exact ⟨Scheme.Modules.tensorSectionsMap K M U.1 (s ⊗ₜ t), hp s t⟩
  have hb := (Scheme.Modules.quasiCoherent_cokernel_image a).2.2.2.2.2.2.2.2 U
  have hi : Set.range ((Scheme.idealModuleProductι i M).app U.1) =
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
/-- Affine quotient projections by positive ideal powers are surjective with the expected
kernel, and their targets are quasi-coherent.
Source: Stacks Project, Tags 01IC and 01AH
(blueprint: lem-weil-pbc-ideal-times-quasi-coherent-affine-sections).
Proof: the ideal-power theorem gives quasi-coherence of the power and its section range.
The tensor and image theorems give quasi-coherence of the product. The preceding range
calculation identifies its inclusion range with the ideal-power multiple. Apply the
quasi-coherent cokernel theorem for quasi-coherence, surjectivity and the kernel formula. -/
private theorem quotient_affine {X : Scheme.{u}} (I : X.IdealSheafData)
    (F : X.Modules) [F.IsQuasicoherent] (U : X.affineOpens) (n : ℕ) (hn : 0 < n) :
    (formalModuleQuotient I n F).IsQuasicoherent ∧
    Function.Surjective ((formalModuleQuotientπ I n F).app U.1) ∧
    LinearMap.ker ((formalModuleQuotientπ I n F).val.app (op U.1)).hom =
      I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1)) := by
  let J := (Scheme.idealSheafPower I.toModulesι n).1
  let i := (Scheme.idealSheafPower I.toModulesι n).2
  have : J.IsQuasicoherent :=
    (Scheme.Modules.ideal_times_quasiCoherent_affine_sections I F).2.2.1 n hn
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  have ht := (Scheme.Modules.quasiCoherent_tensor_product_affine_sections J F).1
  let a := MonoidalCategory.whiskerRight i F ≫ (MonoidalCategory.leftUnitor F).hom
  have hqc : (Scheme.idealModuleProduct i F).IsQuasicoherent := by
    have him := (Scheme.Modules.quasiCoherent_cokernel_image a).2.2.2.2.2.2.2.1
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (Abelian.imageIsoImage a) him
  have hp : (LinearMap.range (i.val.app (op U.1)).hom : Ideal Γ(X, U.1)) =
      I.ideal U ^ n := by
    apply SetLike.coe_injective
    exact ((Scheme.Modules.ideal_times_quasiCoherent_affine_sections I F).2.2.2.1 U).2.2.2 n hn
  have hr := power_multiplication_range i F U
  dsimp only at hr
  rw [hp] at hr
  have hq := Scheme.Modules.quasiCoherent_cokernel_image (Scheme.idealModuleProductι i F)
  refine ⟨hq.2.2.2.2.2.2.1, (hq.2.2.2.2.2.2.2.2 U).2.1, ?_⟩
  change LinearMap.ker ((cokernel.π (Scheme.idealModuleProductι i F)).val.app
    (op U.1)).hom = _
  rw [(hq.2.2.2.2.2.2.2.2 U).2.2.1]
  exact SetLike.coe_injective hr

set_option backward.isDefEq.respectTransparency false in
/-- Kernel part of the reduction torsion bound.
Source: Stacks Project, Remark 0888, final commutative algebra argument.
Proof: restrict to an affine open Spec A. Exact sections on quasi-coherent modules
identify the original and reduced kernels and cokernels with their A-module versions,
and identify ideal products and powers with multiplication by K(U)^t. Put J=I(U)^(n+1).
For f,g in K(U)^t and y in H(U), the cokernel hypothesis gives a lift x with a(x)=fy.
Define h(y)=gx. Two lifts differ in ker(a), so the kernel hypothesis makes h well-defined;
choosing lifts of sums and scalar multiples proves A-linearity. The identities
ah=fg and ha=fg follow respectively from a(x)=fy and the same kernel hypothesis.
Linearity sends JH(U) into JF(U), so h descends modulo J. If a reduced class is in the
kernel, ha=fg shows fg kills it. Such products generate K(U)^(2t); hence that ideal
kills the reduced kernel. The quotient projections identify the reduced map with
formalModuleQuotientMap. Ideal-product vanishing on an affine cover implies vanishing
of the sheaf, yielding the global IsZero statement, uniformly in n.
(blueprint: lem-weil-pbc-coherent-map-reduction-torsion-kernel) -/
theorem coherentMap_reduction_torsion_kernel
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (F H : CoherentModules X) (a : F ⟶ H) (t : ℕ) (ht : 1 ≤ t)
    (hker : IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
      (kernel a.hom)))
    (hcoker : IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
      (cokernel a.hom))) :
    ∀ n : ℕ, IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower K.toModulesι (2 * t)).2
      (kernel (formalModuleQuotientMap I a.hom (Nat.le_refl (n + 1))))) := by
  let : F.obj.IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp F.property).1
  let : H.obj.IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp H.property).1
  let : (kernel a.hom).IsQuasicoherent := Scheme.Modules.isQuasicoherent_kernel a.hom
  let : (cokernel a.hom).IsQuasicoherent :=
    (Scheme.Modules.quasiCoherent_cokernel_image a.hom).2.2.2.2.2.2.1
  have hcover : ∀ x : X, ∃ U ∈ (Set.univ : Set X.affineOpens), x ∈ U.1 := by
    intro x
    obtain ⟨_, ⟨U, hU, rfl⟩, hx, _⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (⊤ : X.Opens) from trivial)
        (⊤ : X.Opens).2
    exact ⟨⟨U, hU⟩, Set.mem_univ _, hx⟩
  have hk := (Scheme.idealPowerProduct_isZero_iff_affine_cover X (kernel a.hom)
    K Set.univ hcover t).mp hker
  have hc := (Scheme.idealPowerProduct_isZero_iff_affine_cover X (cokernel a.hom)
    K Set.univ hcover t).mp hcoker
  intro n
  let b := formalModuleQuotientMap I a.hom (Nat.le_refl (n + 1))
  have hqF := quotient_affine I F.obj
  have hqH := quotient_affine I H.obj
  let : (formalModuleQuotient I (n + 1) F.obj).IsQuasicoherent :=
    (hqF ⟨⊥, isAffineOpen_bot X⟩ (n + 1) (by omega)).1
  let : (formalModuleQuotient I (n + 1) H.obj).IsQuasicoherent :=
    (hqH ⟨⊥, isAffineOpen_bot X⟩ (n + 1) (by omega)).1
  let : (kernel b).IsQuasicoherent := Scheme.Modules.isQuasicoherent_kernel b
  apply (Scheme.idealPowerProduct_isZero_iff_affine_cover X (kernel b)
    K Set.univ hcover (2 * t)).mpr
  intro U _
  let E := SheafOfModules.evaluation X.ringCatSheaf (op U.1)
  let v : Γ(F.obj, U.1) →ₗ[Γ(X, U.1)] Γ(H.obj, U.1) := (E.map a.hom).hom
  let p : Γ(F.obj, U.1) →ₗ[Γ(X, U.1)] Γ(formalModuleQuotient I (n + 1) F.obj, U.1) :=
    (E.map (formalModuleQuotientπ I (n + 1) F.obj)).hom
  let q : Γ(H.obj, U.1) →ₗ[Γ(X, U.1)] Γ(formalModuleQuotient I (n + 1) H.obj, U.1) :=
    (E.map (formalModuleQuotientπ I (n + 1) H.obj)).hom
  let w := (E.map b).hom
  let j := (E.map (kernel.ι b)).hom
  let J := I.ideal U ^ (n + 1)
  have hvk : K.ideal U ^ t ≤ Module.annihilator Γ(X, U.1) (LinearMap.ker v) := by
    intro f hf
    apply Module.mem_annihilator.mpr
    intro z
    obtain ⟨y, hy⟩ := (Set.ext_iff.mp (Scheme.Modules.range_map_kernelι U.1 a.hom)
      (z : Γ(F.obj, U.1))).mpr (LinearMap.mem_ker.mp z.property)
    apply Subtype.ext
    change f • (z : Γ(F.obj, U.1)) = 0
    rw [← hy]
    exact ((E.map (kernel.ι a.hom)).hom.map_smul f y).symm.trans
      (by rw [Module.mem_annihilator.mp (hk U (Set.mem_univ _) hf) y, map_zero])
  have hvc : K.ideal U ^ t ≤ Module.annihilator Γ(X, U.1)
      (Γ(H.obj, U.1) ⧸ LinearMap.range v) := by
    obtain ⟨e, _⟩ :=
      (Scheme.Modules.quasiCoherent_cokernel_image a.hom).2.2.2.2.2.2.2.2 U |>.2.2.2
    intro f hf
    apply Module.mem_annihilator.mpr
    intro z
    apply e.injective
    rw [e.map_smul, e.map_zero]
    exact Module.mem_annihilator.mp (hc U (Set.mem_univ _) hf) (e z)
  obtain ⟨_, hp, hkp⟩ := hqF U (n + 1) (by omega)
  obtain ⟨_, _, hkq⟩ := hqH U (n + 1) (by omega)
  change Function.Surjective p at hp
  change LinearMap.ker p = J • ⊤ at hkp
  change LinearMap.ker q = J • ⊤ at hkq
  have square (z : Γ(F.obj, U.1)) : q (v z) = w (p z) := by
    have hb : formalModuleQuotientπ I (n + 1) F.obj ≫ b =
        a.hom ≫ formalModuleQuotientπ I (n + 1) H.obj := by
      simp [b, formalModuleQuotientπ, formalModuleQuotientMap]
    exact (ConcreteCategory.congr_hom (congrArg E.map hb) z).symm
  have hj (z : Γ(kernel b, U.1)) : w (j z) = 0 := by
    exact (Set.ext_iff.mp (Scheme.Modules.range_map_kernelι U.1 b) (j z)).mp ⟨z, rfl⟩
  rw [two_mul, pow_add]
  refine Ideal.mul_le.mpr fun f hf g hg ↦ Module.mem_annihilator.mpr fun x ↦ ?_
  obtain ⟨z, hz⟩ := hp (j x)
  obtain ⟨k, _, hkv, _, _⟩ :=
    ((LinearMap.ker_coker_annihilated_mod_ideal.{u, u, u, u, u, u, u}
      (K.ideal U) t ht v hvk hvc).1 f g hf hg).2.2
  have hvz : v z ∈ J • (⊤ : Submodule Γ(X, U.1) Γ(H.obj, U.1)) := by
    rw [← hkq]
    exact LinearMap.mem_ker.mpr (by rw [square, hz, hj])
  have hkz : k (v z) ∈ J • (⊤ : Submodule Γ(X, U.1) Γ(F.obj, U.1)) :=
    Submodule.smul_top_le_comap_smul_top J k hvz
  have hfg : (f * g) • z ∈ LinearMap.ker p := by
    rw [hkp]
    have heq := LinearMap.congr_fun hkv z
    change k (v z) = (f * g) • z at heq
    rwa [← heq]
  apply Scheme.Modules.injective_map_kernelι U.1 b
  change j ((f * g) • x) = j 0
  rw [j.map_smul, j.map_zero, ← hz, ← p.map_smul]
  exact LinearMap.mem_ker.mp hfg
end AlgebraicGeometry
