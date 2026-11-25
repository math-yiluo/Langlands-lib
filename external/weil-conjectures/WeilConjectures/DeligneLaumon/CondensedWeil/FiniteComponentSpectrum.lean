/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! Eigenvalues transported through an equivariant dependent-product equivalence. -/

@[expose] public section
set_option autoImplicit false

namespace WeilConjectures.CondensedWeil

/-- An eigenvalue of an endomorphism transported to a finite product is an eigenvalue
on a nonzero component.  This is the linear algebra part of a finite clopen decomposition.
Source: latest blueprint, second paragraph of lem-zl-affine-curve-hc2-purity.proof.md,
the sentence selecting a nonzero summand of an eigenvector
(blueprint: lem-zl-eigenvalue-equiv-pi).
Proof: transport a nonzero eigenvector through phi. Since phi is injective, one of
its coordinates is nonzero. Equivariance and linearity give the eigenvector equation
in that coordinate. Apply its spectral predicate. This also handles the empty product:
there can be no nonzero vector in it. No finiteness assumption is needed. -/
theorem hasEigenvalue_of_equiv_pi
    {K : Type*} [Field K] {H : Type*} [AddCommGroup H] [Module K H]
    {I : Type*}
    (V : I → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (f : ∀ i, Module.End K (V i)) (F : Module.End K H)
    (φ : H ≃ₗ[K] (∀ i, V i))
    (hφ : ∀ (x : H) (i : I), φ (F x) i = f i (φ x i))
    {P : K → Prop} (hP : ∀ (i : I) (a : K),
      Module.End.HasEigenvalue (f i) a → P a)
    {a : K} (ha : Module.End.HasEigenvalue F a) : P a := by
  obtain ⟨x, hxe, hx⟩ := ha.exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff] at hxe
  have hxi : ∃ i, φ x i ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    apply φ.injective
    exact (funext h).trans (map_zero φ).symm
  obtain ⟨i, hxi⟩ := hxi
  apply hP i a
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := φ x i)
  refine Module.End.hasEigenvector_iff.2 ⟨?_, hxi⟩
  rw [Module.End.mem_eigenspace_iff]
  rw [← hφ x i, hxe, map_smul]
  rfl

end WeilConjectures.CondensedWeil
