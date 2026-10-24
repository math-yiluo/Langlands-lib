import Langlands.Shimura.Unitary.ComplexAffineCocharacterComparison
import Langlands.Shimura.Unitary.ComplexWeightSpaces

set_option maxHeartbeats 100000
noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Algebra Module Matrix
open scoped CategoryTheory.MonObj TensorProduct Classical
attribute [local instance 1100] Algebra.toModule

namespace Langlands.GroupScheme.Gm
universe u
variable (R T : Type u) [CommRing R] [CommRing T] [Algebra R T]

/-- Affine section normalization also preserves the inverse of the unit point. -/
theorem relativeAffineUnitPoint_inverse_sections (u : Tˣ) :
    Corepresented.affineSectionsAlgEquiv (R := CommRingCat.of R) (CommAlgCat.of R T)
      ((pointsEquiv _ _ (relativeAffineUnitPoint R T u))⁻¹).val =
        (↑(u⁻¹) : T) := by
  let e := Corepresented.affineSectionsAlgEquiv (R := CommRingCat.of R)
    (CommAlgCat.of R T)
  let v := pointsEquiv _ _ (relativeAffineUnitPoint R T u)
  have h : Units.map e.toMonoidHom v = u :=
    Units.ext (relativeAffineUnitPoint_sections R T u)
  change (Units.map e.toMonoidHom (v⁻¹)).val = _
  exact congrArg Units.val ((map_inv (Units.map e.toMonoidHom) v).trans
    (congrArg Inv.inv h))

end Langlands.GroupScheme.Gm

namespace Langlands.Shimura.CentralSimpleUnitaryData
variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

set_option backward.isDefEq.respectTransparency false in
/-- Affine evaluation retains Kottwitz's conjugation followed by inversion. -/
theorem kottwitzCocharacter_affine_matrices
    (T : Type) [CommRing T] [Algebra ℂ T] [Algebra ℝ T] [IsScalarTower ℝ ℂ T]
    (first : Bool) (u : Tˣ) (τ : E →+* ℝ) :
    D.complexAffinePointMatrices C T
        (D.complexAffineCocharacterValue T (D.kottwitzCocharacter C first) u) τ =
      ComplexMatrix.splitDiagonal T n (if τ = C.distinguished then n - 1 else n)
        (if first then (1, (↑(u⁻¹) : T)) else ((↑(u⁻¹) : T), 1)) := by
  rw [D.complexAffinePointMatrices_sections, complexAffineCocharacterValue,
    D.kottwitzCocharacter_matrices]
  refine (ComplexMatrix.splitDiagonal_map
    (GroupScheme.Corepresented.affineSectionsAlgEquiv (R := CommRingCat.of ℂ)
      (CommAlgCat.of ℂ T)).toRingEquiv.toRingHom n
    (if τ = C.distinguished then n - 1 else n) _).trans ?_
  have h := GroupScheme.Gm.relativeAffineUnitPoint_inverse_sections ℂ T u
  cases first <;> congr 1 <;> apply Prod.ext <;> first | exact h | exact map_one _

/-- Kottwitz matrices at each CM embedding of the actual rational point. -/
theorem kottwitzCocharacter_embedding_matrices (hΦ : IsCMSection E K Φ)
    (first : Bool) (u : ℂˣ) (p : (E →+* ℝ) × Bool) :
    D.complexEmbeddingPointMatrices C hΦ
        (D.complexCocharacterValue (D.kottwitzCocharacter C first) u) (cmFactorEmbedding Φ p) =
      if p.2 then
        (ComplexMatrix.splitDiagonal ℂ n (if p.1 = C.distinguished then n - 1 else n)
          (if first then (1, (↑(u⁻¹) : ℂ)) else ((↑(u⁻¹) : ℂ), 1))).1
      else
        (ComplexMatrix.splitDiagonal ℂ n (if p.1 = C.distinguished then n - 1 else n)
          (if first then (1, (↑(u⁻¹) : ℂ)) else ((↑(u⁻¹) : ℂ), 1))).2 := by
  rw [← D.complexAffineCocharacterValue_rational,
    D.complexEmbeddingPointMatrices_affine, D.kottwitzCocharacter_affine_matrices]

/-- The inverse-weight subspace of the evaluated rational cocharacter at a CM embedding. -/
def kottwitzEmbeddingWeightSpace (hΦ : IsCMSection E K Φ) (i : K →+* ℂ) :
    Submodule ℂ (Fin n → ℂ) :=
  ComplexMatrix.inverseWeightSpace fun u =>
    D.complexEmbeddingPointMatrices C hΦ
      (D.complexCocharacterValue (D.kottwitzCocharacter C true) u) i

/-- Each actual embedding weight space has the corresponding diagonal support. -/
theorem kottwitzEmbeddingWeightSpace_diagonal (hΦ : IsCMSection E K Φ)
    (p : (E →+* ℝ) × Bool) :
    D.kottwitzEmbeddingWeightSpace C hΦ (cmFactorEmbedding Φ p) =
      ComplexMatrix.inverseWeightSpace (fun u : ℂˣ => Matrix.diagonal (fun j : Fin n =>
        if (if p.2 then j.val < (if p.1 = C.distinguished then n - 1 else n)
          else ¬ j.val < (if p.1 = C.distinguished then n - 1 else n))
        then (↑(u⁻¹) : ℂ) else 1)) := by
  unfold kottwitzEmbeddingWeightSpace
  congr 1
  funext u
  rw [D.kottwitzCocharacter_embedding_matrices]
  cases p.2 <;> simp only [Bool.false_eq_true, ↓reduceIte,
    ComplexMatrix.splitDiagonal, ite_not]

/-- The selected and conjugate embeddings have the signature and complementary ranks. -/
theorem finrank_kottwitzEmbeddingWeightSpace_factor (hΦ : IsCMSection E K Φ)
    (p : (E →+* ℝ) × Bool) :
    Module.finrank ℂ (D.kottwitzEmbeddingWeightSpace C hΦ (cmFactorEmbedding Φ p)) =
      if p.2 then (if p.1 = C.distinguished then n - 1 else n)
      else (if p.1 = C.distinguished then 1 else 0) := by
  rw [D.kottwitzEmbeddingWeightSpace_diagonal,
    ComplexMatrix.finrank_inverseWeightSpace_diagonal]
  cases p.2
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _),
      Fin.card_filter_val_lt, min_eq_right (by split_ifs <;> omega),
      Finset.card_univ, Fintype.card_fin]
    have hn := C.rank_gt_one
    split_ifs <;> omega
  · simp only [↓reduceIte, Fin.card_filter_val_lt]
    exact min_eq_right (by split_ifs <;> omega)

/-- Actual embedding-labelled cocharacter weight ranks recover the real Hodge function. -/
theorem finrank_kottwitzEmbeddingWeightSpace (hΦ : IsCMSection E K Φ) (i : K →+* ℂ) :
    Module.finrank ℂ (D.kottwitzEmbeddingWeightSpace C hΦ i) =
      D.realHodgeFunction C i := by
  let p := (cmFactorEmbeddingEquiv Φ hΦ).symm i
  have hp : cmFactorEmbedding Φ p = i := (cmFactorEmbeddingEquiv Φ hΦ).apply_symm_apply i
  rw [← hp, D.finrank_kottwitzEmbeddingWeightSpace_factor, D.realHodgeFunction_eq,
    C.hodgeFunction_apply, realPlaceBelow_cmFactorEmbedding Φ hΦ]
  have hb : p.2 = true ↔ cmFactorEmbedding Φ p = Φ p.1 := by
    have h := cmFactorEmbeddingEquiv_symm_snd Φ hΦ (cmFactorEmbedding Φ p)
    have he : (cmFactorEmbeddingEquiv Φ hΦ).symm (cmFactorEmbedding Φ p) = p :=
      (cmFactorEmbeddingEquiv Φ hΦ).symm_apply_apply p
    rw [he, realPlaceBelow_cmFactorEmbedding Φ hΦ] at h
    exact h
  simp only [hb]

end Langlands.Shimura.CentralSimpleUnitaryData
