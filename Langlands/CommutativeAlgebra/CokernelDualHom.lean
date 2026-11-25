import Langlands.MathlibBase

/-! # The module representing the kernel of a map of finite projective modules after base change -/

universe u

open TensorProduct

namespace Langlands.CommutativeAlgebra.CokernelDualHom

variable {A : Type u} [CommRing A] {K₀ K₁ : Type u} [AddCommGroup K₀] [Module A K₀]
  [Module.Finite A K₀] [Module.Projective A K₀] [AddCommGroup K₁] [Module A K₁]
  [Module.Finite A K₁] [Module.Projective A K₁] (δ : K₀ →ₗ[A] K₁)

/-- For a finite projective `K`, the elements of `B ⊗ K` are the `A`-linear maps `K^∨ → B`:
`b ⊗ k ↦ (φ ↦ φ k • b)`. -/
noncomputable def tensorEquivHom (B : Type u) [CommRing B] [Algebra A B] (K : Type u)
    [AddCommGroup K] [Module A K] [Module.Finite A K] [Module.Projective A K] :
    B ⊗[A] K ≃ₗ[A] (Module.Dual A K →ₗ[A] B) :=
  (TensorProduct.comm A B K).trans
    ((LinearEquiv.rTensor B (Module.evalEquiv A K)).trans
      (dualTensorHomEquiv A (Module.Dual A K) B))

lemma tensorEquivHom_tmul (B : Type u) [CommRing B] [Algebra A B] (K : Type u)
    [AddCommGroup K] [Module A K] [Module.Finite A K] [Module.Projective A K]
    (b : B) (k : K) (φ : Module.Dual A K) :
    tensorEquivHom B K (b ⊗ₜ k) φ = φ k • b := by
  simp [tensorEquivHom]

/-- The module `Q = K₀^∨ ⧸ δ^∨(K₁^∨)`. -/
abbrev Q := Module.Dual A K₀ ⧸ LinearMap.range δ.dualMap

lemma tensorEquivHom_naturality (B : Type u) [CommRing B] [Algebra A B] (x : B ⊗[A] K₀) :
    (tensorEquivHom B K₀ x).comp δ.dualMap = tensorEquivHom B K₁ (δ.lTensor B x) := by
  induction x using TensorProduct.inductionOn with
  | tmul b k =>
    ext ψ
    simp [tensorEquivHom_tmul]
  | add x y hx hy =>
    rw [map_add, LinearMap.add_comp, hx, hy, map_add, map_add]

/-- **The defining property of `Q`.** For an `A`-algebra `B`, the `A`-linear maps `Q → B` are
the elements of `B ⊗ K₀` killed by `δ`. -/
noncomputable def homEquiv (B : Type u) [CommRing B] [Algebra A B] :
    (Q δ →ₗ[A] B) ≃ {x : B ⊗[A] K₀ // δ.lTensor B x = 0} where
  toFun u := ⟨(tensorEquivHom B K₀).symm (u.comp (Submodule.mkQ _)), by
    apply (tensorEquivHom B K₁).injective
    rw [← tensorEquivHom_naturality, LinearEquiv.apply_symm_apply, map_zero]
    ext ψ
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.zero_apply]
    rw [(Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self _ ψ), map_zero]⟩
  invFun x := (LinearMap.range δ.dualMap).liftQ (tensorEquivHom B K₀ x.1) (by
    rintro _ ⟨ψ, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, tensorEquivHom_naturality, x.2, map_zero,
      LinearMap.zero_apply])
  left_inv u := by
    apply Submodule.linearMap_qext
    simp
  right_inv x := by
    apply Subtype.ext
    simp

lemma tensorEquivHom_rTensor {B B' : Type u} [CommRing B] [Algebra A B] [CommRing B']
    [Algebra A B'] (φ : B →ₐ[A] B') (K : Type u) [AddCommGroup K] [Module A K] [Module.Finite A K]
    [Module.Projective A K] (y : B ⊗[A] K) :
    tensorEquivHom B' K (φ.toLinearMap.rTensor K y) = φ.toLinearMap ∘ₗ tensorEquivHom B K y := by
  induction y using TensorProduct.inductionOn with
  | tmul b k =>
    ext ψ
    simp [tensorEquivHom_tmul]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add, LinearMap.comp_add]

/-- **Naturality of `homEquiv`** in the algebra. -/
lemma homEquiv_comp {B B' : Type u} [CommRing B] [Algebra A B] [CommRing B'] [Algebra A B']
    (φ : B →ₐ[A] B') (u : Q δ →ₗ[A] B) :
    (homEquiv δ B' (φ.toLinearMap ∘ₗ u)).1 = φ.toLinearMap.rTensor K₀ (homEquiv δ B u).1 := by
  apply (tensorEquivHom B' K₀).injective
  rw [tensorEquivHom_rTensor]
  change tensorEquivHom B' K₀ ((tensorEquivHom B' K₀).symm _) =
    φ.toLinearMap ∘ₗ tensorEquivHom B K₀ ((tensorEquivHom B K₀).symm _)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, LinearMap.comp_assoc]

lemma tensorEquivHom_smul (B : Type u) [CommRing B] [Algebra A B] (K : Type u)
    [AddCommGroup K] [Module A K] [Module.Finite A K] [Module.Projective A K]
    (c : B) (y : B ⊗[A] K) :
    tensorEquivHom B K (c • y) = c • tensorEquivHom B K y := by
  induction y using TensorProduct.inductionOn with
  | tmul b k =>
    ext ψ
    rw [TensorProduct.smul_tmul', tensorEquivHom_tmul, LinearMap.smul_apply, tensorEquivHom_tmul,
      smul_eq_mul, smul_eq_mul]
    rw [Algebra.smul_def, Algebra.smul_def]
    ring
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- `homEquiv` is linear over the algebra. -/
lemma homEquiv_smul (B : Type u) [CommRing B] [Algebra A B] (c : B) (u : Q δ →ₗ[A] B) :
    (homEquiv δ B (c • u)).1 = c • (homEquiv δ B u).1 := by
  apply (tensorEquivHom B K₀).injective
  rw [tensorEquivHom_smul]
  change tensorEquivHom B K₀ ((tensorEquivHom B K₀).symm _) =
    c • tensorEquivHom B K₀ ((tensorEquivHom B K₀).symm _)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rfl

end Langlands.CommutativeAlgebra.CokernelDualHom
