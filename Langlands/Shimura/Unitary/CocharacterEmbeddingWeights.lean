import Langlands.Shimura.Unitary.ComplexAffineKottwitz
import Langlands.Shimura.Unitary.ComplexWeightConjugacy

noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Algebra Matrix
open scoped CategoryTheory.MonObj Classical

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
  (hΦ : IsCMSection E K Φ)

/-- The matrix at a CM embedding is a unit for every actual complex group point. -/
def complexEmbeddingPointUnit (i : K →+* ℂ) :
    ((algSpec (CommRingCat.of ℚ)).obj (op (CommAlgCat.of ℚ ℂ)) ⟶
      D.rationalGroupScheme.X) →* (Matrix (Fin n) (Fin n) ℂ)ˣ :=
  (show _ →* Matrix (Fin n) (Fin n) ℂ from
    { toFun := fun x => D.complexEmbeddingPointMatrices C hΦ x i
      map_one' := congrFun (map_one (D.complexEmbeddingPointMatrices C hΦ)) i
      map_mul' := fun x y =>
        congrFun (map_mul (D.complexEmbeddingPointMatrices C hΦ) x y) i }).toHomUnits

/-- The constructed unit has exactly the original matrix coordinate. -/
theorem complexEmbeddingPointUnit_val (i : K →+* ℂ)
    (g : (algSpec (CommRingCat.of ℚ)).obj (op (CommAlgCat.of ℚ ℂ)) ⟶
      D.rationalGroupScheme.X) :
    (D.complexEmbeddingPointUnit C hΦ i g : Matrix (Fin n) (Fin n) ℂ) =
      D.complexEmbeddingPointMatrices C hΦ g i := rfl

/-- The inverse unit is the matrix of the inverse actual group point. -/
theorem complexEmbeddingPointUnit_inv_val (i : K →+* ℂ)
    (g : (algSpec (CommRingCat.of ℚ)).obj (op (CommAlgCat.of ℚ ℂ)) ⟶
      D.rationalGroupScheme.X) :
    (↑((D.complexEmbeddingPointUnit C hΦ i g)⁻¹) : Matrix (Fin n) (Fin n) ℂ) =
      D.complexEmbeddingPointMatrices C hΦ g⁻¹ i := rfl

/-- The inverse-weight space at a CM embedding for a family of actual group points. -/
def complexEmbeddingWeightSpace
    (a : ℂˣ → ((algSpec (CommRingCat.of ℚ)).obj (op (CommAlgCat.of ℚ ℂ)) ⟶
      D.rationalGroupScheme.X)) (i : K →+* ℂ) : Submodule ℂ (Fin n → ℂ) :=
  ComplexMatrix.inverseWeightSpace fun u => D.complexEmbeddingPointMatrices C hΦ (a u) i

/-- Conjugation by an actual group point transports each embedding weight space linearly. -/
def complexEmbeddingWeightSpaceConjEquiv
    (a : ℂˣ → ((algSpec (CommRingCat.of ℚ)).obj (op (CommAlgCat.of ℚ ℂ)) ⟶
      D.rationalGroupScheme.X)) (i : K →+* ℂ)
    (g : (algSpec (CommRingCat.of ℚ)).obj (op (CommAlgCat.of ℚ ℂ)) ⟶
      D.rationalGroupScheme.X) :
    D.complexEmbeddingWeightSpace C hΦ a i ≃ₗ[ℂ]
      D.complexEmbeddingWeightSpace C hΦ (fun u => g * a u * g⁻¹) i := by
  have hf : (fun u => D.complexEmbeddingPointMatrices C hΦ (g * a u * g⁻¹) i) =
      (fun u => (D.complexEmbeddingPointUnit C hΦ i g : Matrix (Fin n) (Fin n) ℂ) *
        D.complexEmbeddingPointMatrices C hΦ (a u) i *
        (↑((D.complexEmbeddingPointUnit C hΦ i g)⁻¹) : Matrix (Fin n) (Fin n) ℂ)) := by
    funext u
    rw [map_mul, map_mul]
    rfl
  unfold complexEmbeddingWeightSpace
  rw [hf]
  exact ComplexMatrix.inverseWeightSpaceConjEquiv
    (fun u => D.complexEmbeddingPointMatrices C hΦ (a u) i)
    (D.complexEmbeddingPointUnit C hΦ i g)

/-- Each embedding weight rank is constant under conjugation by an actual group point. -/
theorem finrank_complexEmbeddingWeightSpace_conj
    (a : ℂˣ → ((algSpec (CommRingCat.of ℚ)).obj (op (CommAlgCat.of ℚ ℂ)) ⟶
      D.rationalGroupScheme.X)) (i : K →+* ℂ)
    (g : (algSpec (CommRingCat.of ℚ)).obj (op (CommAlgCat.of ℚ ℂ)) ⟶
      D.rationalGroupScheme.X) :
    Module.finrank ℂ (D.complexEmbeddingWeightSpace C hΦ (fun u => g * a u * g⁻¹) i) =
      Module.finrank ℂ (D.complexEmbeddingWeightSpace C hΦ a i) :=
  (D.complexEmbeddingWeightSpaceConjEquiv C hΦ a i g).finrank_eq.symm

/-- Embedding-labelled inverse-weight space of a cocharacter in the direct complex model. -/
def directCocharacterWeightSpace
    (χ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶
      D.rationalBaseChange rationalComplexBaseMap) (i : K →+* ℂ) :
    Submodule ℂ (Fin n → ℂ) :=
  D.complexEmbeddingWeightSpace C hΦ (D.directComplexCocharacterValue χ) i

/-- Embedding-labelled inverse-weight space of a cocharacter in the iterated complex model. -/
def complexCocharacterWeightSpace
    (χ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶
      D.complexRationalGroupScheme) (i : K →+* ℂ) : Submodule ℂ (Fin n → ℂ) :=
  D.complexEmbeddingWeightSpace C hΦ (D.complexCocharacterValue χ) i

/-- The canonical direct-model comparison preserves the actual weight submodule. -/
theorem complexCocharacterWeightSpace_comparison
    (χ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶
      D.complexRationalGroupScheme) (i : K →+* ℂ) :
    D.complexCocharacterWeightSpace C hΦ χ i =
      D.directCocharacterWeightSpace C hΦ (χ ≫ D.complexDirectGroupSchemeIso.hom) i := rfl

/-- The first-factor Kottwitz cocharacter recovers the established embedding weight space. -/
theorem complexCocharacterWeightSpace_kottwitz (i : K →+* ℂ) :
    D.complexCocharacterWeightSpace C hΦ (D.kottwitzCocharacter C true) i =
      D.kottwitzEmbeddingWeightSpace C hΦ i := rfl

/-- The ranks of the actual Kottwitz cocharacter weight spaces equal the real Hodge function. -/
theorem finrank_complexCocharacterWeightSpace_kottwitz (i : K →+* ℂ) :
    Module.finrank ℂ
      (D.complexCocharacterWeightSpace C hΦ (D.kottwitzCocharacter C true) i) =
      D.realHodgeFunction C i :=
  D.finrank_kottwitzEmbeddingWeightSpace C hΦ i

/-- Every pointwise conjugate of the Kottwitz cocharacter family has the same Hodge ranks. -/
theorem finrank_complexEmbeddingWeightSpace_conj_kottwitz (i : K →+* ℂ)
    (g : (algSpec (CommRingCat.of ℚ)).obj (op (CommAlgCat.of ℚ ℂ)) ⟶
      D.rationalGroupScheme.X) :
    Module.finrank ℂ (D.complexEmbeddingWeightSpace C hΦ
      (fun u => g * D.complexCocharacterValue (D.kottwitzCocharacter C true) u * g⁻¹) i) =
      D.realHodgeFunction C i := by
  rw [D.finrank_complexEmbeddingWeightSpace_conj]
  exact D.finrank_kottwitzEmbeddingWeightSpace C hΦ i

end Langlands.Shimura.CentralSimpleUnitaryData
