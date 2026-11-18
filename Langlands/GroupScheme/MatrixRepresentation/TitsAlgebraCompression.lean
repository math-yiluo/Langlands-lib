import Langlands.Algebra.GaloisTwistedCompression
import Langlands.GroupScheme.MatrixRepresentation.TitsAlgebraFixed

/-! # Tits algebras of compressed representations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

open Algebra.GaloisTwistedMatrix

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {N r : Type} [Fintype N] [DecidableEq N] [Fintype r] [DecidableEq r]

/-- If the coefficient matrices of `ρ'` are the compressions `F X E` of those of `ρ`, and the
Tits algebra of `ρ` lies in a twisted-fixed `k`-form `B` containing `E F`, then the Tits algebra
of `ρ'` is the compression of `B`. -/
theorem titsAlgebra_eq_compressed
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) N)
    (ρ' : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) r)
    (hirr : ρ'.IsIrreducible)
    (hscalar : ∀ C : Matrix r r K, ρ'.Intertwines ρ' C → ∃ c : K, C = Matrix.scalar r c)
    (P' : (K ≃ₐ[k] K) → Matrix r r K) (hP'u : ∀ σ, IsUnit (P' σ))
    (hP' : ∀ σ, ρ'.Intertwines (galoisTwist σ ρ') (P' σ))
    (B : Subalgebra k (Matrix N N K)) (P : (K ≃ₐ[k] K) → Matrix N N K)
    (hPu : ∀ σ, IsUnit (P σ)) (hB : B ≤ twistedFixed P) (hρB : titsAlgebra ρ ≤ B)
    (F : Matrix r N K) (E : Matrix N r K) (hFE : F * E = 1) (hf : E * F ∈ B)
    (hcomp : ∀ φ, coefficientMatrix ρ' φ = F * coefficientMatrix ρ φ * E) :
    titsAlgebra ρ' = compressed B F E hFE hf := by
  have hle : titsAlgebra ρ' ≤ compressed B F E hFE hf := by
    rw [titsAlgebra, Algebra.adjoin_le_iff]
    rintro _ ⟨φ, rfl⟩
    rw [hcomp]
    exact mem_compressed (hρB (Algebra.subset_adjoin ⟨φ, rfl⟩))
  have hC := compressed_le_twistedFixed hB F E hFE hf
  have hCu := isUnit_compressed_twist hB hPu F E hFE hf
  have := finiteDimensional _ hCu (compressed B F E hFE hf) hC
  apply Subalgebra.toSubmodule_injective
  apply Submodule.eq_of_le_of_finrank_le hle
  change Module.finrank k (compressed B F E hFE hf) ≤ Module.finrank k (titsAlgebra ρ')
  rw [finrank_titsAlgebra ρ' hirr hscalar P' hP'u hP']
  have h1 := finrank_twistedFixed_le _ hCu
  have h2 : Module.finrank k (compressed B F E hFE hf) ≤
      Module.finrank k (twistedFixed (fun σ => F.map σ * P σ * E)) := by
    have := finiteDimensional _ hCu (twistedFixed (fun σ => F.map σ * P σ * E)) le_rfl
    exact Submodule.finrank_mono (Subalgebra.toSubmodule.monotone hC)
  exact h2.trans h1

end Langlands.GroupScheme.MatrixRepresentation
