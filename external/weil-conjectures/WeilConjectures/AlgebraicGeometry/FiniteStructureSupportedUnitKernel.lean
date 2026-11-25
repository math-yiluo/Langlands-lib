/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion

/-! # Factor a reduced finite structure unit through a supporting quotient

Source: Stacks Project, Tag 09ZT, algebra structure paragraph, using Tags 01BG and 0096.
(blueprint: lem-weil-pbc-finite-structure-supported-unit-kernel).
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] tensorPullback tensorPullbackObj

open Limits Opposite TopologicalSpace in
open scoped TensorProduct in
private theorem supported_kernel_scalar_annihilation_affine
    {X Z S : Scheme.{u}} (k : Z ⟶ X) [IsClosedImmersion k]
    (j : S ⟶ X) (G : X.Modules) [G.IsQuasicoherent]
    (hkill : ∀ (U : X.Opens) (a : Γ(X, U)), a ∈ k.ker.idealOfOpens U →
      ∀ s : Γ(G, U), a • s = 0)
    (V : X.affineOpens) (U : S.affineOpens) (hUV : U.1 ≤ j ⁻¹ᵁ V.1) :
    ∀ (s : Γ((tensorPullback j).obj (kernel
      (SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom)), U.1))
      (t : Γ((tensorPullback j).obj G, U.1)),
      let a : Γ(S, U.1) := ((tensorPullback j).map
        (kernel.ι (SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom)) ≫
        tensorPullbackObjUnitToUnit j).app U.1 s
      a • t = 0 := by
  classical
  let q : SheafOfModules.unit X.ringCatSheaf ⟶
      (pushforward k).obj (SheafOfModules.unit Z.ringCatSheaf) :=
    SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom
  let K : X.Modules := kernel q
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let i : K ⟶ O := kernel.ι q
  have hO : O.IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have : (SheafOfModules.unit Z.ringCatSheaf).IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_unit (R := Z.ringCatSheaf)
  have hP : ((pushforward k).obj (SheafOfModules.unit Z.ringCatSheaf)).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isClosedImmersion k _
  have hK : K.IsQuasicoherent := isQuasicoherent_kernel q
  let : Algebra Γ(X, V.1) Γ(S, U.1) := (j.appLE V.1 U.1 hUV).hom.toAlgebra
  let : ∀ M : X.Modules, Module Γ(X, V.1) Γ((tensorPullback j).obj M, U.1) :=
    fun M ↦ Module.compHom _ (j.appLE V.1 U.1 hUV).hom
  obtain ⟨c, hc, hb, ht, hn⟩ := exists_tensorPullback_affine_sections j V U hUV
  let α : (tensorPullback j).obj K ⟶ SheafOfModules.unit S.ringCatSheaf :=
    (tensorPullback j).map i ≫ tensorPullbackObjUnitToUnit j
  have hu (a : Γ(X, V.1)) (b : Γ(S, U.1)) :
      (tensorPullbackObjUnitToUnit j).app U.1 (c O hO (a ⊗ₜ b)) =
        b * (j.appLE V.1 U.1 hUV).hom a := by
    rw [ht]
    rw [Hom.app_smul]
    have he := (tensorPullbackObjUnitToUnit_isIso j).2
    have hev := congrArg (fun f ↦ f.val.app (op V.1) a) he
    have hr := congrArg (fun f ↦ f
      (((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app O).val.app
        (op V.1) a))
      ((tensorPullbackObjUnitToUnit j).mapPresheaf.naturality (homOfLE hUV).op)
    change (tensorPullbackObjUnitToUnit j).app U.1
      (((tensorPullback j).obj O).presheaf.map (homOfLE hUV).op
        (((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app O).val.app
          (op V.1) a)) = _ at hr
    rw [hr]
    change b * S.presheaf.map (homOfLE hUV).op
      ((tensorPullbackObjUnitToUnit j).app (j ⁻¹ᵁ V.1)
        (((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app O).val.app
          (op V.1) a)) = _
    change (tensorPullbackObjUnitToUnit j).app (j ⁻¹ᵁ V.1)
        (((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app O).val.app
          (op V.1) a) = (j.app V.1).hom a at hev
    rw [hev]
    rfl
  have ha (x : Γ(K, V.1)) : (i.app V.1 x : Γ(X, V.1)) ∈ k.ker.idealOfOpens V.1 := by
    rw [Scheme.IdealSheafData.idealOfOpens_eq_ideal, k.ker_apply]
    change (k.app V.1).hom (i.app V.1 x) = 0
    exact congrArg (fun f ↦ f.val.app (op V.1) x) (kernel.condition q)
  have hi (x : Γ(K, V.1)) (b : Γ(S, U.1)) :
      α.app U.1 (c K hK (x ⊗ₜ b)) = b * (j.appLE V.1 U.1 hUV).hom (i.app V.1 x) := by
    change (tensorPullbackObjUnitToUnit j).app U.1
      (((tensorPullback j).map i).app U.1 (c K hK (x ⊗ₜ b))) = _
    rw [hn, TensorProduct.map_tmul, LinearMap.id_apply]
    exact hu _ _
  intro s t
  obtain ⟨ss, rfl⟩ := (hc K hK).surjective s
  obtain ⟨tt, rfl⟩ := (hc G inferInstance).surjective t
  let A : Γ((tensorPullback j).obj K, U.1) →ₗ[Γ(S, U.1)] Γ(S, U.1) := α.appₗ U.1
  change A (c K hK ss) • c G inferInstance tt = 0
  change ∀ (x : Γ(K, V.1)) (b : Γ(S, U.1)),
    A (c K hK (x ⊗ₜ b)) = b * (j.appLE V.1 U.1 hUV).hom (i.app V.1 x) at hi
  induction ss using TensorProduct.inductionOn with
  | add s s' hs hs' => simp only [map_add, add_smul, hs, hs', add_zero]
  | tmul x b =>
    rw [hi, mul_smul]
    suffices (j.appLE V.1 U.1 hUV).hom (i.app V.1 x) • c G inferInstance tt = 0 by
      rw [this, smul_zero]
    let r : Γ(X, V.1) := i.app V.1 x
    change r • c G inferInstance tt = 0
    rw [← LinearMap.map_smul]
    change c G inferInstance (r • tt) = 0
    induction tt using TensorProduct.inductionOn with
    | add z z' hz hz' => simp only [smul_add, map_add, hz, hz', add_zero]
    | tmul y d =>
      rw [TensorProduct.smul_tmul', hkill V.1 _ (ha x) y, TensorProduct.zero_tmul, map_zero]

open Limits Opposite TopologicalSpace in
/-- Scalars in the image of the pulled-back kernel annihilate the pullback of G.
Source: Stacks Project, Tags 01BG and 0096, the scalar extension step of Tag 09ZT.

Proof: Let K be the kernel of O_X to k_*O_Z. It is quasi-coherent because the unit
and its closed-immersion pushforward are quasi-coherent. On an affine V, the image
of K(V) is ker(k.app V), which is k.ker.ideal V. Thus hkill annihilates G(V).
Choose an affine U inside j inverse V. The affine pullback comparison identifies
sections of j^*K and j^*G with tensor extensions of K(V) and G(V). The structure
unit sends the pure tensor x tensor b to b times j.appLE applied to the kernel
inclusion of x. Its action on y tensor c is the tensor of the original scalar
acting on y, multiplied by bc; this vanishes by hkill. Tensor induction extends
the calculation to arbitrary pairs of sections. Paired affine opens form a basis;
restriction naturality and sheaf separatedness extend annihilation to every open.
The argument applies to empty opens, the zero module, and the zero or unit ideal.
This theorem does not mention any algebra, finite morphism, or isomorphism to one.
(blueprint: lem-weil-pbc-finite-structure-supported-unit-kernel). -/
private theorem supported_kernel_scalar_annihilation
    {X Z S : Scheme.{u}} (k : Z ⟶ X) [IsClosedImmersion k]
    (j : S ⟶ X) (G : X.Modules) [G.IsQuasicoherent]
    (hkill : ∀ (U : X.Opens) (a : Γ(X, U)), a ∈ k.ker.idealOfOpens U →
      ∀ s : Γ(G, U), a • s = 0) :
    ∀ (U : S.Opens) (s : Γ((tensorPullback j).obj (
      CategoryTheory.Limits.kernel (SheafOfModules.unitToPushforwardObjUnit
        k.toRingCatSheafHom)), U)) (t : Γ((tensorPullback j).obj G, U)),
      let a : Γ(S, U) := ((tensorPullback j).map
        (CategoryTheory.Limits.kernel.ι
          (SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom)) ≫
      tensorPullbackObjUnitToUnit j).app U s
      a • t = 0 := by
  intro W s t
  let M := (tensorPullback j).obj (kernel
    (SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom))
  let N := (tensorPullback j).obj G
  let α : M ⟶ SheafOfModules.unit S.ringCatSheaf :=
    (tensorPullback j).map
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom)) ≫
      tensorPullbackObjUnitToUnit j
  let a : Γ(S, W) := α.app W s
  change a • t = 0
  let B := {b : X.affineOpens × S.affineOpens //
    b.2.1 ≤ j ⁻¹ᵁ b.1.1 ∧ b.2.1 ≤ W}
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩
    (fun b : B ↦ b.1.2.1) W (fun b ↦ homOfLE b.2.2) ?_ _ _ ?_
  · intro x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (j x)) isOpen_univ
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ W ⊓ j ⁻¹ᵁ V from ⟨hx, hxV⟩) (W ⊓ j ⁻¹ᵁ V).2
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨⟨(⟨V, hV⟩, ⟨U, hU⟩), hUW.trans inf_le_right,
        hUW.trans inf_le_left⟩, hxU⟩
  · intro b
    rw [map_zero, Scheme.Modules.map_smul]
    have hn := congrArg (fun f ↦ f s)
      (α.mapPresheaf.naturality (homOfLE b.2.2).op)
    change α.app b.1.2.1 (M.presheaf.map (homOfLE b.2.2).op s) =
      S.presheaf.map (homOfLE b.2.2).op a at hn
    rw [← hn]
    exact supported_kernel_scalar_annihilation_affine k j G hkill b.1.1 b.1.2 b.2.1
      (M.presheaf.map (homOfLE b.2.2).op s) (N.presheaf.map (homOfLE b.2.2).op t)


/-- A reduced structure unit kills the pulled-back kernel of a supporting quotient.
Source: Stacks Project, Tag 09ZT, algebra structure paragraph, using Tags 01BG and 0096.

Proof: Write J for the kernel ideal of the closed immersion k. The canonical map
q is the sheaf quotient O_X to k_*O_Z, so its kernel is J as a module sheaf.
The hypothesis that J kills G makes the multiplication J tensor G to G zero:
on pure section tensors this is exactly hkill, and sheafification extends the
calculation. Pullback preserves quasi-coherence (01BG). On affine charts, tensor
extension identifies the pulled-back product image with multiplication by the
extended ideal on j^*G. Since pullback sends a zero map to zero,
the extended ideal annihilates j^*G. Transport this fact along psi to p_*O_Y.
On paired affine opens V in X and U in S with U contained in j inverse V,
the image of j^*J to O_S consists of the ideal generated by the images of J(V).
Each such scalar annihilates every section of p_*O_Y on U. Apply it to 1:
its image under p's structure ring map is zero. Consequently the composite
j^*J to j^*O_X to O_S to p_*O_Y vanishes on these affine opens. They form a
basis (first choose V near j(x), then U inside its inverse image), so sheaf
separatedness makes the composite zero globally. This is the displayed kernel
inclusion equation. No map O_X to G is constructed. For G zero, the algebra
p_*O_Y is zero and the same argument applies. If J is zero its source kernel
is zero; if J is the unit ideal the reduced algebra is zero. Empty schemes
and empty opens are covered by the same identities.
(blueprint: lem-weil-pbc-finite-structure-supported-unit-kernel). -/
theorem finiteStructure_supported_unit_kernel_zero
    {X Z S Y : Scheme.{u}} (k : Z ⟶ X) [IsClosedImmersion k]
    (j : S ⟶ X) (p : Y ⟶ S) [IsFinite p]
    (G : X.Modules) [G.IsQuasicoherent]
    (hkill : ∀ (U : X.Opens) (a : Γ(X, U)), a ∈ k.ker.idealOfOpens U →
      ∀ s : Γ(G, U), a • s = 0)
    (ψ : (tensorPullback j).obj G ≅
      (pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf)) :
    (tensorPullback j).map
        (CategoryTheory.Limits.kernel.ι
          (SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom)) ≫
      tensorPullbackObjUnitToUnit j ≫
        SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom = 0 := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  let a : Γ(S, U) := (((tensorPullback j).map
        (CategoryTheory.Limits.kernel.ι
          (SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom)) ≫
      tensorPullbackObjUnitToUnit j).app U) s
  let t : Γ((pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf), U) := (1 : Γ(Y, p ⁻¹ᵁ U))
  have h := supported_kernel_scalar_annihilation k j G hkill U s (ψ.inv.app U t)
  have h' := congrArg (ψ.hom.app U) h
  change (ψ.hom.val.app (Opposite.op U)).hom (a • ψ.inv.app U t) =
    (ψ.hom.val.app (Opposite.op U)).hom 0 at h'
  rw [LinearMap.map_smul, map_zero] at h'
  have ht : ψ.hom.app U (ψ.inv.app U t) = t := by
    have hh := congrArg (fun f ↦ f.app U t) ψ.inv_hom_id
    exact hh
  change a • ψ.hom.app U (ψ.inv.app U t) = 0 at h'
  rw [ht] at h'
  change (p.app U).hom a = 0
  change (p.app U).hom a * 1 = 0 at h'
  simpa only [mul_one] using h'

end AlgebraicGeometry.Scheme.Modules
