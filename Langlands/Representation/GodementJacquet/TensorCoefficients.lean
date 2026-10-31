import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Langlands.Representation.Tensor.SmoothDualSurjectivityProof
import Langlands.Representation.GodementJacquet.Zeta

/-! # Product expansions of actual external-tensor coefficients -/

noncomputable section

open scoped TensorProduct

namespace Langlands.GodementJacquet

universe uI uG uV

variable {ι : Type uI} [Fintype ι]
variable {G : ι → Type uG} [∀ i, Group (G i)]
variable [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
variable {V : ι → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- Products of actual coefficients from smooth factor functionals. -/
def productCoefficientGenerators (ρ : ∀ i, Representation ℂ (G i) (V i)) :
    Set ((∀ i, G i) → ℂ) :=
  {f | ∃ (ℓ : ∀ i, SmoothDual (ρ i)) (v : ∀ i, V i),
    (fun g => ∏ i, matrixCoefficient (ρ i) (smoothDualPairing (ρ i) (ℓ i))
      (v i) (g i)) = f}

/-- Every coefficient of the external tensor with a smooth functional has a
finite complex-linear expansion in products of factor coefficients. -/
theorem matrixCoefficient_external_mem_product_span
    (ρ : ∀ i, Representation ℂ (G i) (V i))
    (hρ : ∀ i, IsAdmissible (ρ i))
    (hcof : ∀ i (K : OpenSubgroup (G i)), ∃ L : OpenSubgroup (G i),
      IsCompact (L : Set (G i)) ∧ L ≤ K)
    (ℓ : SmoothDual (FiniteTensor.external ρ)) (v : ⨂[ℂ] i, V i) :
    matrixCoefficient (FiniteTensor.external ρ)
      (smoothDualPairing _ ℓ) v ∈ Submodule.span ℂ (productCoefficientGenerators ρ) := by
  obtain ⟨x, rfl⟩ := FiniteTensor.smoothDualTensorMap_surjective ρ hρ hcof ℓ
  induction x using PiTensorProduct.induction_on with
  | smul_tprod a ℓ =>
    simp only [map_smul, LinearMap.smul_apply]
    apply Submodule.smul_mem
    induction v using PiTensorProduct.induction_on with
    | smul_tprod b v =>
      simp only [map_smul]
      apply Submodule.smul_mem
      apply Submodule.subset_span
      refine ⟨ℓ, v, ?_⟩
      funext g
      exact (FiniteTensor.matrixCoefficient_smoothDualTensorMap_tprod ρ ℓ v g).symm
    | add v w hv hw =>
      simpa only [map_add] using Submodule.add_mem _ hv hw
  | add x y hx hy =>
    simpa only [map_add, LinearMap.add_apply] using Submodule.add_mem _ hx hy

/-- The entire actual bi-smooth coefficient space of the external tensor is
exactly the finite span of products of factor coefficients. -/
theorem biSmoothMatrixCoefficients_external
    (ρ : ∀ i, Representation ℂ (G i) (V i))
    (hρ : ∀ i, IsAdmissible (ρ i))
    (hcof : ∀ i (K : OpenSubgroup (G i)), ∃ L : OpenSubgroup (G i),
      IsCompact (L : Set (G i)) ∧ L ≤ K) :
    biSmoothMatrixCoefficients (FiniteTensor.external ρ) =
      Submodule.span ℂ (productCoefficientGenerators ρ) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨ℓ, v, rfl⟩
    exact matrixCoefficient_external_mem_product_span ρ hρ hcof ℓ v.val
  · apply Submodule.span_le.mpr
    rintro f ⟨ℓ, v, rfl⟩
    apply Submodule.subset_span
    refine ⟨FiniteTensor.smoothDualTensorMap ρ (PiTensorProduct.tprod ℂ ℓ),
      ⟨PiTensorProduct.tprod ℂ v,
        FiniteTensor.isSmooth_external ρ (fun i => (hρ i).1) _⟩, ?_⟩
    funext g
    exact FiniteTensor.matrixCoefficient_smoothDualTensorMap_tprod ρ ℓ v g

/-- An explicit finite sum of products, with all factor functionals smooth. -/
theorem exists_finite_productCoefficient_expansion
    (ρ : ∀ i, Representation ℂ (G i) (V i))
    (hρ : ∀ i, IsAdmissible (ρ i))
    (hcof : ∀ i (K : OpenSubgroup (G i)), ∃ L : OpenSubgroup (G i),
      IsCompact (L : Set (G i)) ∧ L ≤ K)
    (f : biSmoothMatrixCoefficients (FiniteTensor.external ρ)) :
    ∃ (S : Finset ((∀ i, G i) → ℂ)) (a : S → ℂ)
      (ℓ : S → ∀ i, SmoothDual (ρ i)) (v : S → ∀ i, V i),
      ∀ g, f.val g = ∑ j : S, a j * ∏ i,
        matrixCoefficient (ρ i) (smoothDualPairing (ρ i) (ℓ j i)) (v j i) (g i) := by
  classical
  have hf : f.val ∈ Submodule.span ℂ (productCoefficientGenerators ρ) := by
    rw [← biSmoothMatrixCoefficients_external ρ hρ hcof]
    exact f.property
  obtain ⟨a, S, hS, _, hsum⟩ :=
    Submodule.mem_span_iff_exists_finset_subset.mp hf
  have hS' : ∀ j : S, ∃ (ℓ : ∀ i, SmoothDual (ρ i)) (v : ∀ i, V i),
      (fun g => ∏ i, matrixCoefficient (ρ i) (smoothDualPairing (ρ i) (ℓ i))
        (v i) (g i)) = j.val := fun j => hS j.property
  choose ℓ v hv using hS'
  refine ⟨S, fun j => a j.val, ℓ, v, fun g => ?_⟩
  calc
    f.val g = ∑ j ∈ S, a j * j g := by
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
        (congrFun hsum g).symm
    _ = ∑ j : S, a j.val * j.val g := (Finset.sum_coe_sort S _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [congrFun (hv j) g]

end Langlands.GodementJacquet
