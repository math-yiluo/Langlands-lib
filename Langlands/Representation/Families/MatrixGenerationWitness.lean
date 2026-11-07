import Langlands.Representation.Plancherel.FiniteMatrixOpennessProof
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Determinant witnesses for generation of a specialized matrix algebra

The coefficient algebra is any commutative complex algebra. A finite collection
of words in the matrix generators determines a determinant in that algebra.
Its nonvanishing forces the specialized generators to generate all matrices.
-/

noncomputable section

universe uB uJ un uσ

namespace Langlands.Renard.AlgebraicFamily.MatrixGenerationWitness

variable {B : Type uB} [CommRing B] [Algebra ℂ B]
  {J : Type uJ} {n : Type un} [Fintype n] [DecidableEq n]

/-- The matrices obtained by applying a complex-valued character to each entry. -/
def specialize (A : J → Matrix n n B) (χ : B →ₐ[ℂ] ℂ) :
    J → Matrix n n ℂ :=
  fun j => χ.mapMatrix (A j)

/-- The columns are flattened matrices given by the selected words. -/
def wordMatrix (A : J → Matrix n n B) (w : n × n → FreeAlgebra ℂ J) :
    Matrix (n × n) (n × n) B :=
  fun i j => FreeAlgebra.lift ℂ A (w j) i.1 i.2

/-- A determinant whose nonvanishing certifies full matrix-algebra generation. -/
def wordDeterminant (A : J → Matrix n n B) (w : n × n → FreeAlgebra ℂ J) : B :=
  (wordMatrix A w).det

/-- Evaluation of words commutes with specialization of the matrix generators. -/
theorem specialize_lift (A : J → Matrix n n B) (χ : B →ₐ[ℂ] ℂ)
    (w : FreeAlgebra ℂ J) :
    χ.mapMatrix (FreeAlgebra.lift ℂ A w) =
      FreeAlgebra.lift ℂ (specialize A χ) w := by
  have h : χ.mapMatrix.comp (FreeAlgebra.lift ℂ A) =
      FreeAlgebra.lift ℂ (specialize A χ) := by
    apply FreeAlgebra.hom_ext
    funext j
    simp [specialize]
  exact DFunLike.congr_fun h w

/-- The witness specializes to the determinant of the specialized word matrix. -/
theorem specialize_wordDeterminant (A : J → Matrix n n B)
    (w : n × n → FreeAlgebra ℂ J) (χ : B →ₐ[ℂ] ℂ) :
    χ (wordDeterminant A w) = wordDeterminant (specialize A χ) w := by
  unfold wordDeterminant
  rw [AlgHom.map_det]
  congr 1
  ext i j
  exact congrArg (fun M : Matrix n n ℂ => M i.1 i.2)
    (specialize_lift A χ (w j))

/-- Nonvanishing of a word determinant implies full specialized matrix generation. -/
theorem adjoin_eq_top_of_wordDeterminant_ne_zero (A : J → Matrix n n B)
    (w : n × n → FreeAlgebra ℂ J) (χ : B →ₐ[ℂ] ℂ)
    (hw : χ (wordDeterminant A w) ≠ 0) :
    Algebra.adjoin ℂ (Set.range (specialize A χ)) = ⊤ := by
  classical
  have hd : (wordMatrix (specialize A χ) w).det ≠ 0 := by
    rwa [specialize_wordDeterminant] at hw
  have hs : Function.Surjective (wordMatrix (specialize A χ) w).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd))
  apply top_unique
  intro M _
  obtain ⟨v, hv⟩ := hs (fun i : n × n => M i.1 i.2)
  have hM : (∑ j, v j • FreeAlgebra.lift ℂ (specialize A χ) (w j)) = M := by
    ext i j
    have h := congrFun hv (i, j)
    simpa [Matrix.mulVec, dotProduct, wordMatrix, Matrix.sum_apply, mul_comm] using h
  rw [← hM]
  apply Subalgebra.sum_mem
  intro j _
  apply Subalgebra.smul_mem
  rw [Algebra.adjoin_range_eq_range_freeAlgebra_lift]
  exact ⟨w j, rfl⟩

/-- If the specialized generators act irreducibly, some word determinant is one
at that character. This also covers the empty matrix index type. -/
theorem exists_wordDeterminant_eq_one (A : J → Matrix n n B)
    (χ₀ : B →ₐ[ℂ] ℂ)
    (h₀ : UnitarizabilityContinuation.IsIrreducibleFamily (specialize A χ₀)) :
    ∃ w : n × n → FreeAlgebra ℂ J, χ₀ (wordDeterminant A w) = 1 := by
  classical
  have htop :=
    (Plancherel.FiniteMatrixOpenness.matrix_irreducible_iff_adjoin_eq_top _).mp h₀
  have hs : Function.Surjective (FreeAlgebra.lift ℂ (specialize A χ₀)) := by
    apply (AlgHom.range_eq_top _).mp
    rwa [← Algebra.adjoin_range_eq_range_freeAlgebra_lift]
  choose w hw using fun i : n × n => hs (Matrix.stdBasis ℂ n n i)
  refine ⟨w, ?_⟩
  rw [specialize_wordDeterminant]
  have hid : wordMatrix (specialize A χ₀) w = 1 := by
    ext i j
    change FreeAlgebra.lift ℂ (specialize A χ₀) (w j) i.1 i.2 = _
    rw [hw j]
    rcases j with ⟨j, k⟩
    rw [Matrix.stdBasis_eq_single]
    simp [Matrix.single, Matrix.one_apply, Prod.ext_iff, eq_comm]
  simp [wordDeterminant, hid]

/-- The determinant witness gives a principal nonvanishing neighborhood of an
irreducible specialization, throughout which all specializations are irreducible. -/
theorem exists_principal_neighborhood (A : J → Matrix n n B)
    (χ₀ : B →ₐ[ℂ] ℂ)
    (h₀ : UnitarizabilityContinuation.IsIrreducibleFamily (specialize A χ₀)) :
    ∃ f : B, χ₀ f = 1 ∧ ∀ χ : B →ₐ[ℂ] ℂ, χ f ≠ 0 →
      UnitarizabilityContinuation.IsIrreducibleFamily (specialize A χ) := by
  obtain ⟨w, hw⟩ := exists_wordDeterminant_eq_one A χ₀ h₀
  refine ⟨wordDeterminant A w, hw, fun χ hχ => ?_⟩
  exact (Plancherel.FiniteMatrixOpenness.matrix_irreducible_iff_adjoin_eq_top _).mpr
    (adjoin_eq_top_of_wordDeterminant_ne_zero A w χ hχ)

end Langlands.Renard.AlgebraicFamily.MatrixGenerationWitness
