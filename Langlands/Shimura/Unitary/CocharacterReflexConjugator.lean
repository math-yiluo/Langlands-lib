import Langlands.Shimura.Unitary.ComplexPointSplitting
import Langlands.Shimura.Unitary.CocharacterReflexNecessity
import Langlands.Shimura.Unitary.KottwitzPointMultiplier

noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Algebra Matrix
open scoped CategoryTheory.MonObj Classical TensorProduct

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
  (hΦ : IsCMSection E K Φ)

/-- The inverse-weight support at an arbitrary CM embedding. -/
def kottwitzEmbeddingSupport (i : K →+* ℂ) (j : Fin n) : Prop :=
  let p := (cmFactorEmbeddingEquiv Φ hΦ).symm i
  if p.2 then j.val < (if p.1 = C.distinguished then n - 1 else n)
    else ¬ j.val < (if p.1 = C.distinguished then n - 1 else n)

/-- Each embedding matrix is the inverse/trivial diagonal on its actual support. -/
theorem kottwitzCocharacterValue_diagonal (i : K →+* ℂ) (u : ℂˣ) :
    D.complexEmbeddingPointMatrices C hΦ
      (D.complexCocharacterValue (D.kottwitzCocharacter C true) u) i =
        Matrix.diagonal (fun j => if D.kottwitzEmbeddingSupport C hΦ i j
          then (↑(u⁻¹) : ℂ) else 1) := by
  let p := (cmFactorEmbeddingEquiv Φ hΦ).symm i
  have hp : cmFactorEmbedding Φ p = i := (cmFactorEmbeddingEquiv Φ hΦ).apply_symm_apply i
  rw [← hp, D.kottwitzCocharacter_embedding_matrices]
  simp only [kottwitzEmbeddingSupport,
    show (cmFactorEmbeddingEquiv Φ hΦ).symm (cmFactorEmbedding Φ p) = p from
      (cmFactorEmbeddingEquiv Φ hΦ).symm_apply_apply p]
  cases p.2 <;> simp only [Bool.false_eq_true, ↓reduceIte,
    ComplexMatrix.splitDiagonal, ite_not]

/-- Support cardinality is the previously identified real Hodge multiplicity. -/
theorem card_kottwitzEmbeddingSupport (i : K →+* ℂ) :
    (Finset.univ.filter (D.kottwitzEmbeddingSupport C hΦ i)).card =
      D.realHodgeFunction C i := by
  have h := D.finrank_kottwitzEmbeddingWeightSpace C hΦ i
  unfold kottwitzEmbeddingWeightSpace at h
  have hf := funext (D.kottwitzCocharacterValue_diagonal C hΦ i)
  rw [hf, ComplexMatrix.finrank_inverseWeightSpace_diagonal] at h
  exact h

/-- The rational coefficient action cancels substitution in each diagonal family. -/
theorem kottwitzCocharacterValue_diagonal_galois (s : ℂ ≃ₐ[ℚ] ℂ)
    (i : K →+* ℂ) (u : ℂˣ) :
    s.toRingEquiv.mapMatrix
      (D.complexEmbeddingPointMatrices C hΦ
        (D.complexCocharacterValue (D.kottwitzCocharacter C true)
          (Units.map s.symm.toMonoidHom u)) i) =
      Matrix.diagonal (fun j => if D.kottwitzEmbeddingSupport C hΦ i j
        then (↑(u⁻¹) : ℂ) else 1) := by
  rw [D.kottwitzCocharacterValue_diagonal C hΦ]
  ext j k
  simp only [RingEquiv.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

/-- Preserving Hodge multiplicities gives a single matrix conjugator at each shifted embedding. -/
theorem exists_galois_kottwitz_factor_conjugator (s : ℂ ≃ₐ[ℚ] ℂ)
    (hs : s ∈ hodgeStabilizer (D.realHodgeFunction C)) (i : K →+* ℂ) :
    ∃ g : (Matrix (Fin n) (Fin n) ℂ)ˣ, ∀ u : ℂˣ,
      (g : Matrix (Fin n) (Fin n) ℂ) *
        D.complexEmbeddingPointMatrices C hΦ
          (D.complexCocharacterValue
            (D.galoisCocharacter s (D.kottwitzCocharacter C true)) u)
          ((s : ℂ →+* ℂ).comp i) *
        (↑(g⁻¹) : Matrix (Fin n) (Fin n) ℂ) =
      D.complexEmbeddingPointMatrices C hΦ
        (D.complexCocharacterValue (D.kottwitzCocharacter C true) u)
        ((s : ℂ →+* ℂ).comp i) := by
  let p := D.kottwitzEmbeddingSupport C hΦ i
  let q := D.kottwitzEmbeddingSupport C hΦ ((s : ℂ →+* ℂ).comp i)
  have hc : (Finset.univ.filter p).card = (Finset.univ.filter q).card := by
    exact (D.card_kottwitzEmbeddingSupport C hΦ i).trans
      ((hs i).symm.trans (D.card_kottwitzEmbeddingSupport C hΦ _).symm)
  let c := C.embeddingChartConjugator hΦ D.totallyRealBasis s i
  let d := ComplexMatrix.diagonalWeightConjugator p q ℂ hc
  refine ⟨d * c⁻¹, ?_⟩
  intro u
  have hm : D.complexEmbeddingPointMatrices C hΦ
      (D.complexCocharacterValue (D.galoisCocharacter s (D.kottwitzCocharacter C true)) u)
      ((s : ℂ →+* ℂ).comp i) =
        (c : Matrix (Fin n) (Fin n) ℂ) *
          Matrix.diagonal (fun j => if p j then (↑(u⁻¹) : ℂ) else 1) *
            (↑(c⁻¹) : Matrix (Fin n) (Fin n) ℂ) := by
    rw [D.complexCocharacterValue_galois_comparison,
      D.directComplexCocharacterValue_transport,
      D.complexEmbeddingPointMatrices_galois_factor,
      C.embeddingChartComparison_conj]
    change _ * s.toRingEquiv.mapMatrix
      (D.complexEmbeddingPointMatrices C hΦ
        (D.complexCocharacterValue (D.kottwitzCocharacter C true)
          (Units.map s.symm.toMonoidHom u)) i) * _ = _
    rw [D.kottwitzCocharacterValue_diagonal_galois C hΦ]
  rw [hm, D.kottwitzCocharacterValue_diagonal C hΦ]
  simpa only [Units.val_mul, _root_.mul_inv_rev, inv_inv, mul_assoc,
    Units.inv_mul_cancel_left] using
      ComplexMatrix.diagonalWeightConjugator_spec p q ℂ hc u

include hΦ in
/-- Hodge preservation supplies one multiplier-one actual group point for all scalar values. -/
theorem exists_galois_kottwitz_point_conjugator (s : ℂ ≃ₐ[ℚ] ℂ)
    (hs : s ∈ hodgeStabilizer (D.realHodgeFunction C)) :
    ∃ g : (algSpec (CommRingCat.of ℚ)).obj (op (CommAlgCat.of ℚ ℂ)) ⟶
        D.rationalGroupScheme.X,
      D.complexPointMultiplier g = 1 ∧ ∀ u : ℂˣ,
        g * D.complexCocharacterValue
          (D.galoisCocharacter s (D.kottwitzCocharacter C true)) u * g⁻¹ =
        D.complexCocharacterValue (D.kottwitzCocharacter C true) u := by
  have hm (τ : E →+* ℝ) : ∃ g : (Matrix (Fin n) (Fin n) ℂ)ˣ, ∀ u : ℂˣ,
      (g : Matrix (Fin n) (Fin n) ℂ) *
        D.complexEmbeddingPointMatrices C hΦ
          (D.complexCocharacterValue
            (D.galoisCocharacter s (D.kottwitzCocharacter C true)) u) (Φ τ) *
        (↑(g⁻¹) : Matrix (Fin n) (Fin n) ℂ) =
      D.complexEmbeddingPointMatrices C hΦ
        (D.complexCocharacterValue (D.kottwitzCocharacter C true) u) (Φ τ) := by
    have hi : (s : ℂ →+* ℂ).comp ((s.symm : ℂ →+* ℂ).comp (Φ τ)) = Φ τ := by
      ext a
      exact s.apply_symm_apply _
    simpa only [hi] using D.exists_galois_kottwitz_factor_conjugator C hΦ s hs
      ((s.symm : ℂ →+* ℂ).comp (Φ τ))
  choose m hm using hm
  let g := D.complexMatrixPoint C m
  have hg (τ : E →+* ℝ) : D.complexEmbeddingPointUnit C hΦ (Φ τ) g = m τ := by
    apply Units.ext
    exact D.complexMatrixPoint_matrices C hΦ m τ
  refine ⟨g, D.complexMatrixPoint_multiplier C m, ?_⟩
  intro u
  apply D.complexRationalPoint_ext C hΦ
  · intro τ
    change ((D.complexEmbeddingPointUnit C hΦ (Φ τ)
      (g * D.complexCocharacterValue
        (D.galoisCocharacter s (D.kottwitzCocharacter C true)) u * g⁻¹)) :
          Matrix (Fin n) (Fin n) ℂ) = _
    rw [map_mul, map_mul, map_inv, hg]
    exact hm τ u
  · rw [map_mul, map_mul, map_inv,
      D.complexPointMultiplier_galois_kottwitz C,
      D.complexPointMultiplier_kottwitzCocharacterValue C]
    exact mul_inv_cancel_comm _ _

end Langlands.Shimura.CentralSimpleUnitaryData
