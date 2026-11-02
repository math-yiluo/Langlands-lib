import Langlands.Algebra.NilpotentFlatPresentation
import Mathlib.Algebra.Module.Torsion.Basic

universe u v w z

open TensorProduct

namespace Langlands.Algebra

section Quotient

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The usual quotient--tensor comparison, linear over the quotient ring. -/
noncomputable def quotientTensorEquiv (I : Ideal R) :
    ((R ⧸ I) ⊗[R] M) ≃ₗ[R ⧸ I] M ⧸ (I • (⊤ : Submodule R M)) :=
  (TensorProduct.quotTensorEquivQuotSMul M I).extendScalarsOfSurjective
    (Ideal.Quotient.mk_surjective)

@[simp]
theorem quotientTensorEquiv_mk_tmul (I : Ideal R) (r : R) (m : M) :
    quotientTensorEquiv R M I (Ideal.Quotient.mk I r ⊗ₜ[R] m) =
      Submodule.Quotient.mk (r • m) :=
  TensorProduct.quotTensorEquivQuotSMul_mk_tmul I r m

@[simp]
theorem quotientTensorEquiv_symm_mk (I : Ideal R) (m : M) :
    (quotientTensorEquiv R M I).symm (Submodule.Quotient.mk m) = 1 ⊗ₜ[R] m :=
  TensorProduct.quotTensorEquivQuotSMul_symm_mk I m

variable {M}
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- The actual map on ideal-multiple quotients induced by a linear map. -/
noncomputable def quotientReduction (I : Ideal R) (f : M →ₗ[R] N) :
    (M ⧸ (I • (⊤ : Submodule R M))) →ₗ[R ⧸ I]
      N ⧸ (I • (⊤ : Submodule R N)) :=
  (quotientTensorEquiv R N I).toLinearMap ∘ₗ f.baseChange (R ⧸ I) ∘ₗ
    (quotientTensorEquiv R M I).symm.toLinearMap

@[simp]
theorem quotientReduction_mk (I : Ideal R) (f : M →ₗ[R] N) (m : M) :
    quotientReduction R I f (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk (f m) := by
  change quotientTensorEquiv R N I
    (f.baseChange (R ⧸ I) ((quotientTensorEquiv R M I).symm
      (Submodule.Quotient.mk m))) = _
  rw [quotientTensorEquiv_symm_mk, LinearMap.baseChange_tmul]
  exact TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul I (f m)

theorem quotientTensorEquiv_natural (I : Ideal R) (f : M →ₗ[R] N)
    (x : (R ⧸ I) ⊗[R] M) :
    quotientTensorEquiv R N I (f.baseChange (R ⧸ I) x) =
      quotientReduction R I f (quotientTensorEquiv R M I x) := by
  simp [quotientReduction]

end Quotient

section Nilpotent

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
variable (M : Type w) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]

/-- Finite presentation of a base-flat module can be tested on its ordinary
quotient by a nilpotent base ideal. -/
theorem finitePresentation_iff_quotient_smul_of_base_nilpotent
    [Module.Flat A M] (I : Ideal A) (hI : IsNilpotent I) :
    Module.FinitePresentation B M ↔
      Module.FinitePresentation (B ⧸ I.map (algebraMap A B))
        (M ⧸ (I.map (algebraMap A B) • (⊤ : Submodule B M))) := by
  constructor
  · intro h
    exact Module.FinitePresentation.of_equiv
      (quotientTensorEquiv B M (I.map (algebraMap A B)))
  · intro h
    have := Module.FinitePresentation.of_equiv
      (quotientTensorEquiv B M (I.map (algebraMap A B))).symm
    exact finitePresentation_of_base_nilpotent A B I hI

/-- Choose finite free presentation data using finite presentation of the
ordinary quotient as the input. -/
noncomputable def finiteFreePresentationOfNilpotentQuotient
    [Module.Flat A M] (I : Ideal A) (hI : IsNilpotent I)
    [Module.FinitePresentation (B ⧸ I.map (algebraMap A B))
      (M ⧸ (I.map (algebraMap A B) • (⊤ : Submodule B M)))] :
    Σ n : ℕ, Σ m : ℕ,
      {p : ((Fin n → B) →ₗ[B] M) × ((Fin m → B) →ₗ[B] (Fin n → B)) //
        Function.Surjective p.1 ∧ Function.Exact p.2 p.1} := by
  have : Module.FinitePresentation B M :=
    (finitePresentation_iff_quotient_smul_of_base_nilpotent A B M I hI).mpr inferInstance
  apply Classical.choice
  obtain ⟨n, m, f, g, hf, H⟩ := Module.FinitePresentation.exists_fin' B M
  exact ⟨⟨n, m, ⟨(f, g), hf, H⟩⟩⟩

end Nilpotent

end Langlands.Algebra
