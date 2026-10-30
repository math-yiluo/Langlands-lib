import Langlands.Algebra.TensorFiniteExtensionNormStatement
import Langlands.AlgebraicGeometry.Picard.FiniteFieldExtensionNormProof

/-! # Proof of the norm laws on the base change of a finite field extension -/

universe u

open scoped TensorProduct

namespace Langlands.Algebra

open Langlands.AlgebraicGeometry.Picard.FiniteFieldExtensionNorm

/-- Mathlib's `Algebra.norm A` on `A ⊗[K] L` commutes with base change, sends `a` to
`a ^ [L : K]`, and avoids a prime `p` exactly when its argument avoids every prime over `p`. -/
theorem tensorFiniteExtensionNorm : TensorFiniteExtensionNormStatement.{u} := by
  intro K L _ _ _ _ A _ _
  let b := Module.finBasis K L
  refine ⟨?_, ?_, ?_⟩
  · intro B _ _ φ f
    refine norm_map_of_basis (Algebra.TensorProduct.basis A b)
      (Algebra.TensorProduct.basis B b) φ.toRingHom
      (Algebra.TensorProduct.map φ (AlgHom.id K L)).toRingHom (fun a => ?_) (fun i => ?_) f
    · simp [Algebra.TensorProduct.algebraMap_apply]
    · simp [Algebra.TensorProduct.basis_apply]
  · intro a
    rw [Algebra.norm_algebraMap_of_basis (Algebra.TensorProduct.basis A b), Fintype.card_fin]
  · intro f p
    constructor
    · intro hn q hq hf
      apply hn
      rw [← hq]
      exact norm_mem_comap (Algebra.TensorProduct.basis A b) f q.asIdeal hf
    · intro h hn
      obtain ⟨Q, hQ, hQP, hfQ⟩ :=
        exists_prime_over_of_norm_mem (Algebra.TensorProduct.basis A b) f p.asIdeal hn
      exact h ⟨Q, hQ⟩ (PrimeSpectrum.ext hQP) hfQ

end Langlands.Algebra
