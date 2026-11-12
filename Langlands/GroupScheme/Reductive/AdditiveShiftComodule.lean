import Langlands.GroupScheme.Chevalley.SubspaceMatrix

/-! # Elements of a coalgebra shifted by a fixed element under a coefficient map -/

noncomputable section

open TensorProduct Coalgebra Module

namespace Langlands.GroupScheme.AdditiveShift

open AffineLinearEmbedding Chevalley

variable {K : Type*} [Field K] {B : Type*} [CommRing B] [Algebra K B] [Coalgebra K B]

/-- Comultiplication commutes with right translation, by coassociativity. -/
theorem comul_rightAct (f : Module.Dual K B) (u : B) :
    comul (R := K) (rightAct f u) = (rightAct f).lTensor B (comul (R := K) u) := by
  have h1 : (comul (R := K) : B →ₗ[K] B ⊗[K] B) ∘ₗ
        ((TensorProduct.rid K B).toLinearMap ∘ₗ f.lTensor B) =
      ((TensorProduct.rid K (B ⊗[K] B)).toLinearMap ∘ₗ f.lTensor (B ⊗[K] B)) ∘ₗ
        (comul (R := K)).rTensor B := by
    ext x y
    simp
  have h3 : ((TensorProduct.rid K (B ⊗[K] B)).toLinearMap ∘ₗ f.lTensor (B ⊗[K] B)) ∘ₗ
        (TensorProduct.assoc K B B B).symm.toLinearMap =
      ((TensorProduct.rid K B).toLinearMap ∘ₗ f.lTensor B).lTensor B := by
    apply TensorProduct.ext_threefold'
    intro x y z
    simp
  calc comul (R := K) (rightAct f u)
      = ((comul (R := K) : B →ₗ[K] B ⊗[K] B) ∘ₗ
          ((TensorProduct.rid K B).toLinearMap ∘ₗ f.lTensor B)) (comul (R := K) u) := rfl
    _ = ((TensorProduct.rid K (B ⊗[K] B)).toLinearMap ∘ₗ f.lTensor (B ⊗[K] B))
          ((comul (R := K)).rTensor B (comul (R := K) u)) := by
        rw [h1]
        rfl
    _ = ((TensorProduct.rid K (B ⊗[K] B)).toLinearMap ∘ₗ f.lTensor (B ⊗[K] B))
          ((TensorProduct.assoc K B B B).symm ((comul (R := K)).lTensor B (comul (R := K) u))) := by
        rw [coassoc_symm_apply]
    _ = (((TensorProduct.rid K B).toLinearMap ∘ₗ f.lTensor B).lTensor B)
          ((comul (R := K)).lTensor B (comul (R := K) u)) :=
        LinearMap.congr_fun h3 _
    _ = (rightAct f).lTensor B (comul (R := K) u) := by
        rw [← LinearMap.lTensor_comp_apply]
        rfl

variable {C : Type*} [CommRing C] [Algebra K C] (φ : B →ₐ[K] C) (ψ : C)

/-- `u` is shifted by `a • ψ` under left translation along `φ`: in coordinates,
`u(n x) = u(x) + a ψ(n)`. -/
def IsShift (u : B) (a : K) : Prop :=
  (φ.toLinearMap.rTensor B) (comul (R := K) u) = (1 : C) ⊗ₜ[K] u + a • (ψ ⊗ₜ[K] (1 : B))

variable {φ ψ}

/-- Restricting a shifted element along `φ` gives its counit plus the shift. -/
theorem IsShift.map_eq {u : B} {a : K} (h : IsShift φ ψ u a)
    (hε1 : counit (R := K) (1 : B) = 1) :
    φ u = algebraMap K C (counit (R := K) u) + a • ψ := by
  have h2 := congrArg (fun t => TensorProduct.rid K C ((counit (R := K)).lTensor C t)) h
  have hl : TensorProduct.rid K C ((counit (R := K)).lTensor C
      ((φ.toLinearMap.rTensor B) (comul (R := K) u))) = φ u := by
    rw [← LinearMap.comp_apply ((counit (R := K)).lTensor C), LinearMap.lTensor_comp_rTensor,
      ← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply, lTensor_counit_comul]
    simp
  rw [hl] at h2
  rw [h2]
  simp [hε1, Algebra.smul_def, mul_comm]

/-- Right translation preserves shifted elements, scaling the shift by the value at `1`. -/
theorem IsShift.rightAct {u : B} {a : K} (h : IsShift φ ψ u a)
    (hone : comul (R := K) (1 : B) = (1 : B) ⊗ₜ[K] (1 : B)) (f : Module.Dual K B) :
    IsShift φ ψ (rightAct f u) (a * f 1) := by
  unfold IsShift at h ⊢
  rw [comul_rightAct, ← LinearMap.comp_apply (φ.toLinearMap.rTensor B),
    LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply, h]
  have h1 : AffineLinearEmbedding.rightAct f (1 : B) = f 1 • (1 : B) := by
    rw [rightAct_apply, hone]
    simp
  simp [h1, mul_smul]

variable (φ ψ) in
/-- The subspace of elements shifted by a scalar multiple of `ψ`. -/
def shiftSubmodule : Submodule K B where
  carrier := {u | ∃ a, IsShift φ ψ u a}
  zero_mem' := ⟨0, by simp [IsShift]⟩
  add_mem' := by
    rintro u v ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    unfold IsShift at ha hb ⊢
    rw [map_add, map_add, ha, hb, tmul_add, add_smul]
    abel
  smul_mem' := by
    rintro c u ⟨a, ha⟩
    refine ⟨c * a, ?_⟩
    unfold IsShift at ha ⊢
    rw [map_smul, map_smul, ha, smul_add, tmul_smul, mul_smul]

/-- The right translates of a shifted element span a subspace of shifted elements. -/
theorem regularSpan_le_shiftSubmodule {h : B} (hh : IsShift φ ψ h 1)
    (hone : comul (R := K) (1 : B) = (1 : B) ⊗ₜ[K] (1 : B)) :
    regularSpan (K := K) {h} ≤ shiftSubmodule φ ψ := by
  rw [regularSpan, Submodule.span_le]
  rintro _ ⟨⟨⟨x, hx⟩, f⟩, rfl⟩
  rw [Finset.mem_singleton] at hx
  subst hx
  exact ⟨1 * f 1, hh.rightAct hone f⟩

variable (φ) in
/-- The shift coefficient read off with a functional `λ` normalized by `λ ψ = 1`. -/
def shiftCoeff (lam : Module.Dual K C) : Module.Dual K B :=
  lam.comp φ.toLinearMap - lam 1 • counit (R := K)

theorem IsShift.eq_shiftCoeff {u : B} {a : K} (h : IsShift φ ψ u a)
    (hε1 : counit (R := K) (1 : B) = 1) {lam : Module.Dual K C} (hlam : lam ψ = 1) :
    a = shiftCoeff φ lam u := by
  have h2 := congrArg lam (h.map_eq hε1)
  simp only [map_add, map_smul, hlam, smul_eq_mul, mul_one] at h2
  rw [shiftCoeff, LinearMap.sub_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, h2,
    LinearMap.smul_apply, Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- The counit expansion of a basis vector in the matrix coefficients. -/
theorem basis_eq_sum_counit (V : Submodule K B) {N : ℕ} (b : Basis (Fin N) K V)
    (hV : ∀ (f : Module.Dual K B) (v : B), v ∈ V → AffineLinearEmbedding.rightAct f v ∈ V)
    (j : Fin N) :
    (b j : B) = ∑ i, counit (R := K) (b i : B) • subspaceMatrix V b i j := by
  have h := congrArg (fun t => TensorProduct.lid K B ((counit (R := K)).rTensor B t))
    (comul_basis V b hV j)
  simp only [rTensor_counit_comul, TensorProduct.lid_tmul, one_smul, map_sum,
    LinearMap.rTensor_tmul] at h
  exact h

/-- The shift coefficients of a basis of a stable subspace of shifted elements are fixed by the
right-translation matrix coefficients. -/
theorem sum_shiftCoeff_smul_subspaceMatrix (V : Submodule K B) {N : ℕ} (b : Basis (Fin N) K V)
    (hV : ∀ (f : Module.Dual K B) (v : B), v ∈ V → AffineLinearEmbedding.rightAct f v ∈ V)
    (hVs : V ≤ shiftSubmodule φ ψ) (hε1 : counit (R := K) (1 : B) = 1)
    {lam : Module.Dual K C} (hlam : lam ψ = 1) (j : Fin N) :
    ∑ i, shiftCoeff φ lam (b i : B) • subspaceMatrix V b i j =
      shiftCoeff φ lam (b j : B) • (1 : B) := by
  let μ : Module.Dual K B := lam.comp φ.toLinearMap
  -- the left translate by `μ`, computed from the matrix coefficients
  have h1 : leftAct μ (b j : B) = ∑ i, μ (b i : B) • subspaceMatrix V b i j := by
    rw [leftAct_apply, comul_basis V b hV j, map_sum, map_sum]
    simp
  -- the left translate by `μ`, computed from the shift
  have h2 : ∀ {u : B} {a : K}, IsShift φ ψ u a → leftAct μ u = lam 1 • u + a • (1 : B) := by
    intro u a hu
    have : μ.rTensor B = (lam.rTensor B) ∘ₗ (φ.toLinearMap.rTensor B) := by
      rw [← LinearMap.rTensor_comp]
    rw [leftAct_apply, this, LinearMap.comp_apply, hu]
    simp [hlam]
  have hμ : ∀ {u : B} {a : K}, IsShift φ ψ u a →
      μ u = counit (R := K) u * lam 1 + a := by
    intro u a hu
    have := congrArg lam (hu.map_eq hε1)
    simpa [μ, hlam, Algebra.algebraMap_eq_smul_one, mul_comm] using this
  obtain ⟨aj, haj⟩ := hVs (b j).2
  have hshift : ∀ i, IsShift φ ψ (b i : B) (shiftCoeff φ lam (b i : B)) := by
    intro i
    obtain ⟨a, ha⟩ := hVs (b i).2
    rwa [← ha.eq_shiftCoeff hε1 hlam]
  have hcounit := basis_eq_sum_counit V b hV j
  have key := h1.symm.trans (h2 (hshift j))
  simp only [hμ (hshift _)] at key
  have e1 : ∑ i, (counit (R := K) (b i : B) * lam 1 + shiftCoeff φ lam (b i : B)) •
        subspaceMatrix V b i j =
      lam 1 • (b j : B) + ∑ i, shiftCoeff φ lam (b i : B) • subspaceMatrix V b i j := by
    calc ∑ i, (counit (R := K) (b i : B) * lam 1 + shiftCoeff φ lam (b i : B)) •
          subspaceMatrix V b i j
        = ∑ i, (lam 1 • (counit (R := K) (b i : B) • subspaceMatrix V b i j) +
            shiftCoeff φ lam (b i : B) • subspaceMatrix V b i j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [add_smul, mul_comm, mul_smul]
      _ = lam 1 • ∑ i, counit (R := K) (b i : B) • subspaceMatrix V b i j +
            ∑ i, shiftCoeff φ lam (b i : B) • subspaceMatrix V b i j := by
          rw [Finset.sum_add_distrib, Finset.smul_sum]
      _ = lam 1 • (b j : B) + ∑ i, shiftCoeff φ lam (b i : B) • subspaceMatrix V b i j := by
          rw [← hcounit]
  rw [e1] at key
  exact add_left_cancel key

end Langlands.GroupScheme.AdditiveShift
