/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Ideal.Cotangent
import WeilConjectures.AlgebraicGeometry.AffineConormalSections
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Tensor coordinates before the second module pullback

Source: Stacks Project, Morphisms, Tags 0473 and 01R3 (2); Schemes, Tag 01JU (1).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

/-- If a surjective algebra map has kernel extended from an ideal annihilating `M`,
tensoring that map with `M` is bijective. The extended ideal annihilates the tensor
by balancing; tensor right exactness then identifies the kernel with zero. -/
private theorem tensorQuotientBijective
    {A B D M : Type*} [CommRing A] [CommRing B] [CommRing D]
    [Algebra A B] [Algebra A D] [AddCommGroup M] [Module A M]
    (q : B →ₐ[A] D) (hq : Function.Surjective q) (J : Ideal A)
    (hker : RingHom.ker q.toRingHom = J.map (algebraMap A B))
    (hJ : ∀ a ∈ J, ∀ m : M, a • m = 0) :
    Function.Bijective (q.toLinearMap.rTensor M) := by
  have hann : J.map (algebraMap A B) ≤ Module.annihilator B (B ⊗[A] M) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    apply Module.mem_annihilator.mpr
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul b m =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, ← Algebra.smul_def,
        TensorProduct.smul_tmul (R := A) a b m,
        hJ a ha m, TensorProduct.tmul_zero]
    | add x y hx hy => simp only [smul_add, hx, hy, add_zero]
  have hz : (q.toLinearMap.ker.subtype).rTensor M = 0 := by
    ext b m
    change (b : B) ⊗ₜ[A] m = 0
    have hb : (b : B) ∈ J.map (algebraMap A B) := by
      rw [← hker]
      exact b.property
    have he := Module.mem_annihilator.mp (hann hb) ((1 : B) ⊗ₜ[A] m)
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using he
  constructor
  · rw [← LinearMap.ker_eq_bot,
      (rTensor_exact M q.toLinearMap.exact_subtype_ker_map hq).linearMap_ker_eq,
      hz, LinearMap.range_zero]
  · exact LinearMap.rTensor_surjective M hq

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ambient tensor of cotangent classes identifies with the tensor of conormal
sections over the source chart rings. This concerns only the tensor modules, before
applying the section map of the second module pullback.

Source: Stacks Project, Morphisms, Tags 0473 and 01R3 (2); Schemes, Tag 01JU (1).
(blueprint: lem-weil-pbc-closed-immersion-conormal-affine-tensor-coordinates).

Proof: Put A = Γ(X',U'), B = Γ(X,U), J = i'.ker.ideal U',
C = Γ(Z',i'⁻¹U'), and D = Γ(Z,i⁻¹U). Closed immersions make both inverse-image
opens affine and the maps A → C and B → D surjective. The cartesian square gives
ker(B → D) = J.map(A → B), using the pullback projection kernel formula and the
affine ideal-comap formula. Thus C = A/J and D = B/JB, compatibly with C → D.
The affine conormal equivalence identifies N = Γ(i'*i'.ker,i'⁻¹U') with J/J²;
it sends class(a) to the unit on the ideal section representing a and is C-linear,
since it is A-linear and A → C is surjective. Since J annihilates J/J², scalar
cancellation identifies N ⊗[C] D with N ⊗[A] D. The quotient tensor formula
identifies the latter with (B ⊗[A] J/J²)/(JB • ⊤), after swapping factors.
The denominator is zero: g(a) • (b ⊗ m) = b ⊗ (a • m) = 0 for a ∈ J;
linearity extends this from ideal generators and pure tensors. Remove the zero
quotient and compose the equivalences. Their pure-tensor formulas send b ⊗ class(a)
to unit(s') ⊗ i.app(b), proving the normalization. This also covers J = 0, J = A,
and zero chart rings, without a flatness hypothesis. -/
theorem closedImmersion_conormal_affine_tensor_coordinates
    {X Z X' Z' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    [IsClosedImmersion i] [IsClosedImmersion i']
    (g : X ⟶ X') (f : Z ⟶ Z') (h : i ≫ g = f ≫ i')
    (hc : IsLimit (PullbackCone.mk i f h))
    (U : X.affineOpens) (U' : X'.affineOpens) (H : U.1 ≤ g ⁻¹ᵁ U'.1) :
    letI : Algebra Γ(X', U'.1) Γ(X, U.1) := (g.appLE U'.1 U.1 H).hom.toAlgebra
    let V' : Z'.affineOpens := ⟨i' ⁻¹ᵁ U'.1, U'.2.preimage i'⟩
    let V : Z.affineOpens := ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩
    let K : V.1 ≤ f ⁻¹ᵁ V'.1 := by
      change i ⁻¹ᵁ U.1 ≤ f ⁻¹ᵁ i' ⁻¹ᵁ U'.1
      rw [← Scheme.Hom.comp_preimage, ← h, Scheme.Hom.comp_preimage]
      exact i.preimage_mono H
    letI : Algebra Γ(Z', V'.1) Γ(Z, V.1) := (f.appLE V'.1 V.1 K).hom.toAlgebra
    ∃ e : (Γ(X, U.1) ⊗[Γ(X', U'.1)] (i'.ker.ideal U').Cotangent) ≃+
        (Γ((tensorPullback i').obj i'.ker.toModules, V'.1) ⊗[Γ(Z', V'.1)] Γ(Z, V.1)),
      ∀ (b : Γ(X, U.1)) (a : i'.ker.ideal U') (s' : Γ(i'.ker.toModules, U'.1)),
        i'.ker.toModulesι.app U'.1 s' = (a : Γ(X', U'.1)) →
        e (b ⊗ₜ[Γ(X', U'.1)] (i'.ker.ideal U').toCotangent a) =
          (show Γ((tensorPullback i').obj i'.ker.toModules, V'.1) from
            ((Classical.choose (exists_tensorPullbackAdjunction i')).unit.app
              i'.ker.toModules).app U'.1 s') ⊗ₜ[Γ(Z', V'.1)] i.app U.1 b := by
  classical
  dsimp only
  let A := Γ(X', U'.1)
  let B := Γ(X, U.1)
  let J := i'.ker.ideal U'
  let V' : Z'.affineOpens := ⟨i' ⁻¹ᵁ U'.1, U'.2.preimage i'⟩
  let V : Z.affineOpens := ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩
  let K : V.1 ≤ f ⁻¹ᵁ V'.1 := by
    change i ⁻¹ᵁ U.1 ≤ f ⁻¹ᵁ i' ⁻¹ᵁ U'.1
    rw [← Scheme.Hom.comp_preimage, ← h, Scheme.Hom.comp_preimage]
    exact i.preimage_mono H
  let C := Γ(Z', V'.1)
  let D := Γ(Z, V.1)
  let N := Γ((tensorPullback i').obj i'.ker.toModules, V'.1)
  let : Algebra A B := (g.appLE U'.1 U.1 H).hom.toAlgebra
  let : Algebra A C := (i'.app U'.1).hom.toAlgebra
  let : Algebra B D := (i.app U.1).hom.toAlgebra
  let : Algebra A D := ((i.app U.1).hom.comp (g.appLE U'.1 U.1 H).hom).toAlgebra
  let : Algebra C D := (f.appLE V'.1 V.1 K).hom.toAlgebra
  let : Module A N := Module.compHom N (i'.app U'.1).hom
  let : IsScalarTower A C N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : IsScalarTower A B D := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hcomm : (f.appLE V'.1 V.1 K).hom.comp (i'.app U'.1).hom =
      (i.app U.1).hom.comp (g.appLE U'.1 U.1 H).hom := by
    change (i'.app U'.1 ≫ f.appLE V'.1 V.1 K).hom =
      (g.appLE U'.1 U.1 H ≫ i.app U.1).hom
    simp only [V, V', Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, h]
  let : IsScalarTower A C D := IsScalarTower.of_algebraMap_smul fun a d ↦ by
    change ((f.appLE V'.1 V.1 K).hom ((i'.app U'.1).hom a) * d) = _
    have he := RingHom.congr_fun hcomm a
    change (f.appLE V'.1 V.1 K).hom ((i'.app U'.1).hom a) =
      (i.app U.1).hom ((g.appLE U'.1 U.1 H).hom a) at he
    rw [he]
    rfl
  have hi : i.ker.ideal U = J.map (algebraMap A B) := by
    let p : IsPullback i f g i' := IsPullback.of_isLimit hc
    have hk : i.ker = i'.ker.comap g := by
      rw [← p.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
        Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
    rw [hk]
    exact Scheme.IdealSheafData.ideal_comap_appLE i'.ker g U' U H
  have := RingHomInvPair.of_ringEquiv (RingEquiv.refl A)
  have := RingHomInvPair.of_ringEquiv_symm (RingEquiv.refl A)
  obtain ⟨E, hE⟩ := (affine_conormal_sections i').2 U' A (RingEquiv.refl A) J (by
    simp [J, Scheme.Hom.ker_apply])
  let e : J.Cotangent ≃ₗ[A] N := E
  let q : B →ₐ[A] D :=
    { (i.app U.1).hom with commutes' := fun _ ↦ rfl }
  have hq : Function.Surjective q := i.app_surjective U.1 U.2
  have hker : RingHom.ker q.toRingHom = J.map (algebraMap A B) := by
    simpa only [q, Scheme.Hom.ker_apply] using hi
  have hJ : ∀ a ∈ J, ∀ n : N, a • n = 0 := by
    intro a ha n
    obtain ⟨m, rfl⟩ := e.surjective n
    rw [← e.map_smul, Ideal.Cotangent.smul_eq_zero_of_mem ha, map_zero]
  let d := LinearEquiv.ofBijective (q.toLinearMap.rTensor N)
    (tensorQuotientBijective q hq J hker hJ)
  let : TensorProduct.CompatibleSMul A C N D :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective N D (i'.app_surjective U'.1 U'.2)
  let c := TensorProduct.equivOfCompatibleSMul A C A N D
  refine ⟨(TensorProduct.congr (LinearEquiv.refl A B) e).toAddEquiv.trans
    (d.toAddEquiv.trans ((TensorProduct.comm A D N).toAddEquiv.trans c.symm.toAddEquiv)), ?_⟩
  intro b a s hs
  change c.symm (TensorProduct.comm A D N (d (b ⊗ₜ[A] e (J.toCotangent a)))) = _
  change c.symm (e (J.toCotangent a) ⊗ₜ[A] i.app U.1 b) = _
  change e (J.toCotangent a) ⊗ₜ[C] i.app U.1 b = _
  rw [show e (J.toCotangent a) = _ from hE a s hs]

end AlgebraicGeometry.Scheme.Modules
