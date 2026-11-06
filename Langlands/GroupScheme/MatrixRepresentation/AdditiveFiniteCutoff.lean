import Langlands.GroupScheme.MatrixRepresentation.AdditiveGeneratedFullness

/-! # Finite degree cutoffs for full additive coefficient algebras -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation.AdditiveFiniteCutoff

open AdditiveDividedPowers AdditiveTensorAlgebra

variable {k : Type u} [Field k] {I : Type v}
  {n : Type} [Fintype n] [DecidableEq n]
  (ρs : I → MatrixRepresentation (VectorGroup.groupScheme (CommRingCat.of k) 1) n)

/-- Increasing the strict degree bound increases the truncated coefficient algebra. -/
theorem truncatedCoefficientAlgebra_mono :
    Monotone (truncatedCoefficientAlgebra ρs) := by
  intro N N' h
  apply Algebra.adjoin_le
  rintro _ ⟨⟨i, d⟩, rfl⟩
  exact Algebra.subset_adjoin ⟨(i, ⟨d.val, lt_of_lt_of_le d.isLt h⟩), rfl⟩

/-- The directed union of all finite-degree coefficient algebras. -/
def boundedCoefficientAlgebra : Subalgebra k (Matrix n n k) where
  carrier := {M | ∃ N, M ∈ truncatedCoefficientAlgebra ρs N}
  algebraMap_mem' c := ⟨0, (truncatedCoefficientAlgebra ρs 0).algebraMap_mem c⟩
  add_mem' := by
    rintro M T ⟨N, hN⟩ ⟨P, hP⟩
    exact ⟨max N P, (truncatedCoefficientAlgebra ρs (max N P)).add_mem
      (truncatedCoefficientAlgebra_mono ρs (le_max_left N P) hN)
      (truncatedCoefficientAlgebra_mono ρs (le_max_right N P) hP)⟩
  mul_mem' := by
    rintro M T ⟨N, hN⟩ ⟨P, hP⟩
    exact ⟨max N P, (truncatedCoefficientAlgebra ρs (max N P)).mul_mem
      (truncatedCoefficientAlgebra_mono ρs (le_max_left N P) hN)
      (truncatedCoefficientAlgebra_mono ρs (le_max_right N P) hP)⟩

theorem truncatedCoefficientAlgebra_le_coefficientAlgebra (N : ℕ) :
    truncatedCoefficientAlgebra ρs N ≤ coefficientAlgebra ρs := by
  apply Algebra.adjoin_le
  rintro _ ⟨⟨i, d⟩, rfl⟩
  exact coefficientMatrix_mem_coefficientAlgebra ρs i d.val

/-- Every algebra expression uses coefficients below some finite degree bound,
even when the additive family has an infinite index type. -/
theorem boundedCoefficientAlgebra_eq_coefficientAlgebra :
    boundedCoefficientAlgebra ρs = coefficientAlgebra ρs := by
  apply le_antisymm
  · rintro M ⟨N, hN⟩
    exact truncatedCoefficientAlgebra_le_coefficientAlgebra ρs N hN
  · apply Algebra.adjoin_le
    rintro _ ⟨⟨i, d⟩, rfl⟩
    exact ⟨d + 1, Algebra.subset_adjoin ⟨(i, ⟨d, Nat.lt_succ_self d⟩), rfl⟩⟩

/-- Full matrix coefficient algebra already occurs below a finite degree bound. -/
theorem exists_truncatedCoefficientAlgebra_eq_top
    (hfull : coefficientAlgebra ρs = ⊤) :
    ∃ N, truncatedCoefficientAlgebra ρs N = ⊤ := by
  have hb : boundedCoefficientAlgebra ρs = ⊤ :=
    (boundedCoefficientAlgebra_eq_coefficientAlgebra ρs).trans hfull
  have hunits (ij : n × n) :
      ∃ N, Matrix.single ij.1 ij.2 (1 : k) ∈ truncatedCoefficientAlgebra ρs N := by
    change Matrix.single ij.1 ij.2 (1 : k) ∈ boundedCoefficientAlgebra ρs
    rw [hb]
    trivial
  choose Ns hNs using hunits
  let N := Finset.univ.sup Ns
  refine ⟨N, top_unique ?_⟩
  intro M _
  rw [Matrix.matrix_eq_sum_single M]
  apply (truncatedCoefficientAlgebra ρs N).sum_mem
  intro i _
  apply (truncatedCoefficientAlgebra ρs N).sum_mem
  intro j _
  have hunit : Matrix.single i j (1 : k) ∈ truncatedCoefficientAlgebra ρs N :=
    truncatedCoefficientAlgebra_mono ρs
      (Finset.le_sup (f := Ns) (Finset.mem_univ (i, j))) (hNs (i, j))
  simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using
    (truncatedCoefficientAlgebra ρs N).smul_mem hunit (M i j)

/-- Every sufficiently large prime-power degree bound has full coefficients. -/
theorem exists_forall_truncatedCoefficientAlgebra_pow_eq_top
    (p : ℕ) [Fact p.Prime] (hfull : coefficientAlgebra ρs = ⊤) :
    ∃ E, ∀ e, E ≤ e → truncatedCoefficientAlgebra ρs (p ^ e) = ⊤ := by
  obtain ⟨N, hN⟩ := exists_truncatedCoefficientAlgebra_eq_top ρs hfull
  refine ⟨N, fun e he => top_unique ?_⟩
  rw [← hN]
  exact truncatedCoefficientAlgebra_mono ρs
    (he.trans (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le)

section Ambient

variable {G : GroupScheme (Spec (CommRingCat.of k))}
  (ρ : MatrixRepresentation G n)
  (f : I → (VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G))
  (p : ℕ) [Fact p.Prime] [CharP k p]
  [IsAlgClosed k] [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsReduced G.X.left] [Nonempty n]

/-- A fixed actual irreducible first factor has one exponent bound that works
for every actual irreducible second factor and every larger exponent. -/
theorem exists_forall_isIrreducible_tensor_frobeniusPower_of_isGeneratedByFamily
    (hρ : ρ.IsIrreducible)
    (hgen : IsGeneratedByFamily
      (fun _ : I => VectorGroup.groupScheme (CommRingCat.of k) 1) f (𝟙 G)) :
    ∃ E, ∀ e, E ≤ e →
      ∀ {m : Type} [Fintype m] [DecidableEq m] [Nonempty m]
        (σ : MatrixRepresentation G m), σ.IsIrreducible →
          (ρ.tensor (σ.frobeniusPower p e)).IsIrreducible := by
  obtain ⟨E, hE⟩ := exists_forall_truncatedCoefficientAlgebra_pow_eq_top
    (fun i => ρ.restrict (f i)) p
    (AdditiveGeneratedFullness.coefficientAlgebra_eq_top_of_isGeneratedByFamily ρ f p hρ hgen)
  refine ⟨E, ?_⟩
  intro e he m _ _ _ σ hσ
  exact AdditiveGeneratedFullness.isIrreducible_tensor_frobeniusPower_of_isGeneratedByFamily
    ρ f p σ hσ hgen e (hE e he)

/-- The eventual bound gives a cofinal choice of exponents for each supplied
pair of actual irreducible representations. -/
theorem exists_ge_isIrreducible_tensor_frobeniusPower_of_isGeneratedByFamily
    (hρ : ρ.IsIrreducible)
    (hgen : IsGeneratedByFamily
      (fun _ : I => VectorGroup.groupScheme (CommRingCat.of k) 1) f (𝟙 G))
    {m : Type} [Fintype m] [DecidableEq m] [Nonempty m]
    (σ : MatrixRepresentation G m) (hσ : σ.IsIrreducible) (N : ℕ) :
    ∃ e, N ≤ e ∧ (ρ.tensor (σ.frobeniusPower p e)).IsIrreducible := by
  obtain ⟨E, hE⟩ :=
    exists_forall_isIrreducible_tensor_frobeniusPower_of_isGeneratedByFamily ρ f p hρ hgen
  exact ⟨max N E, le_max_left N E, hE _ (le_max_right N E) σ hσ⟩

end Ambient

end Langlands.GroupScheme.MatrixRepresentation.AdditiveFiniteCutoff
