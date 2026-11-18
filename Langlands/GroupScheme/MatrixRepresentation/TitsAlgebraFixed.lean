import Langlands.GroupScheme.MatrixRepresentation.TitsAlgebra

/-! # The Tits algebra is the full twisted-fixed algebra -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix TensorProduct

namespace Langlands.Algebra.GaloisTwistedMatrix

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
  {n : Type} [Fintype n] [DecidableEq n]

/-- The twisted-fixed algebra has dimension at most `n²`. -/
theorem finrank_twistedFixed_le (P : (K ≃ₐ[k] K) → Matrix n n K) (hP : ∀ σ, IsUnit (P σ)) :
    Module.finrank k (twistedFixed P) ≤ Fintype.card n * Fintype.card n := by
  have := finiteDimensional P hP (twistedFixed P) le_rfl
  let b := Module.finBasis k (twistedFixed P)
  have hli : LinearIndependent K (fun i => (b i : Matrix n n K)) :=
    linearIndependent_of_le_twistedFixed P hP _ (fun i => (b i).2)
      (b.linearIndependent.map' (twistedFixed P).val.toLinearMap
        (LinearMap.ker_eq_bot.mpr Subtype.val_injective))
  have h := hli.fintype_card_le_finrank
  rw [Module.finrank_matrix, Module.finrank_self, mul_one, Fintype.card_fin] at h
  exact h

end Langlands.Algebra.GaloisTwistedMatrix

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]

/-- For an irreducible representation with scalar self-intertwiners and invertible
intertwiners `P σ : ρ → ρ^σ`, the Tits algebra is the whole twisted-fixed algebra of `P`. -/
theorem titsAlgebra_eq_twistedFixed
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n)
    (hirr : ρ.IsIrreducible)
    (hscalar : ∀ C : Matrix n n K, ρ.Intertwines ρ C → ∃ c : K, C = Matrix.scalar n c)
    (P : (K ≃ₐ[k] K) → Matrix n n K) (hPunit : ∀ σ, IsUnit (P σ))
    (hP : ∀ σ, ρ.Intertwines (galoisTwist σ ρ) (P σ)) :
    titsAlgebra ρ = Algebra.GaloisTwistedMatrix.twistedFixed P := by
  have hle := titsAlgebra_le_twistedFixed P hP
  have := Algebra.GaloisTwistedMatrix.finiteDimensional P hPunit
    (Algebra.GaloisTwistedMatrix.twistedFixed P) le_rfl
  apply Subalgebra.toSubmodule_injective
  apply Submodule.eq_of_le_of_finrank_le hle
  change Module.finrank k (Algebra.GaloisTwistedMatrix.twistedFixed P) ≤
    Module.finrank k (titsAlgebra ρ)
  rw [finrank_titsAlgebra ρ hirr hscalar P hPunit hP]
  exact Algebra.GaloisTwistedMatrix.finrank_twistedFixed_le P hPunit

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.GroupScheme

open MatrixRepresentation

/-- For every Galois extension `K/k`, affine group `G` over `k` and irreducible representation
`ρ` of `G_K` with scalar self-intertwiners and invertible intertwiners `P σ : ρ → ρ^σ`, the
Tits algebra of `ρ` is the twisted-fixed algebra of `P`. -/
def TitsAlgebraEqTwistedFixedStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [IsGalois k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom] (n : ℕ)
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) (Fin n)),
    ρ.IsIrreducible →
    (∀ C : Matrix (Fin n) (Fin n) K, ρ.Intertwines ρ C → ∃ c : K, C = Matrix.scalar (Fin n) c) →
    ∀ (P : (K ≃ₐ[k] K) → Matrix (Fin n) (Fin n) K), (∀ σ, IsUnit (P σ)) →
      (∀ σ, ρ.Intertwines (galoisTwist σ ρ) (P σ)) →
        titsAlgebra ρ = Algebra.GaloisTwistedMatrix.twistedFixed P

theorem titsAlgebraEqTwistedFixed : TitsAlgebraEqTwistedFixedStatement.{u} := by
  intro k K _ _ _ _ G _ n ρ hirr hscalar P hPunit hP
  exact titsAlgebra_eq_twistedFixed ρ hirr hscalar P hPunit hP

end Langlands.GroupScheme
