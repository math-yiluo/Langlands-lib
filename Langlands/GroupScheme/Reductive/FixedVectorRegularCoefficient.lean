import Langlands.GroupScheme.Chevalley.CoefficientEmbedding
import Langlands.GroupScheme.MatrixRepresentation.NormalFixedCoordinates

/-! # Sending a nonzero fixed vector to the constant regular function -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct Coalgebra Module
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.Chevalley

open AffineLinearEmbedding MatrixRepresentation

variable {k : Type u} [Field k]
  {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  {n : Type} [Fintype n] [DecidableEq n]

/-- A normalized row of the universal coefficient matrix. -/
def normalizedCoefficientFamily
    (ρ : MatrixRepresentation (Corepresented.groupScheme F e) n)
    (v : n → k) (i : n) : n → B :=
  fun j => (v i)⁻¹ • Unipotent.universalMatrix e ρ i j

/-- Normalizing a coefficient row does not change its coaction equation. -/
theorem normalizedCoefficientFamily_comul
    (ρ : MatrixRepresentation (Corepresented.groupScheme F e) n)
    (v : n → k) (i j : n) :
    letI := (bialgebra e).toCoalgebra
    comul (R := k) (normalizedCoefficientFamily e ρ v i j) =
      ∑ l, normalizedCoefficientFamily e ρ v i l ⊗ₜ[k]
        Unipotent.universalMatrix e ρ l j := by
  let := (bialgebra e).toCoalgebra
  change AffineLinearEmbedding.comul e ((v i)⁻¹ • Unipotent.universalMatrix e ρ i j) =
    ∑ l, ((v i)⁻¹ • Unipotent.universalMatrix e ρ i l) ⊗ₜ[k]
      Unipotent.universalMatrix e ρ l j
  rw [map_smul, Unipotent.comul_universalMatrix]
  simp only [Finset.smul_sum, TensorProduct.smul_tmul']

/-- The normalized coefficient map sends the fixed vector to the constant one. -/
theorem normalizedCoefficientFamily_fixed
    (ρ : MatrixRepresentation (Corepresented.groupScheme F e) n)
    (v : n → k) (hv : ρ.IsFixedVector v) (i : n) (hi : v i ≠ 0) :
    ∑ j, v j • normalizedCoefficientFamily e ρ v i j = (1 : B) := by
  have h := congrFun (hv.affine B (𝟙 _)) i
  have hrow : ∑ j, v j • Unipotent.universalMatrix e ρ i j =
      v i • (1 : B) := by
    simpa only [Unipotent.universalMatrix, Matrix.mulVec, dotProduct,
      Algebra.smul_def, mul_one, one_mul, mul_comm] using h
  calc
    _ = (v i)⁻¹ • ∑ j, v j • Unipotent.universalMatrix e ρ i j := by
      simp only [normalizedCoefficientFamily, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
    _ = (v i)⁻¹ • (v i • (1 : B)) := by rw [hrow]
    _ = 1 := by rw [smul_smul, inv_mul_cancel₀ hi, one_smul]

/-- A nonzero fixed vector maps to the constant one in an actual finite regular
representation. The source representation need not embed in the coordinate ring. -/
theorem exists_finite_regular_map_to_one
    (ρ : MatrixRepresentation (Corepresented.groupScheme F e) n)
    (v : n → k) (hv0 : v ≠ 0) (hv : ρ.IsFixedVector v) :
    ∃ (V : Submodule k B) (d : ℕ) (b : Basis (Fin d) k V)
      (hV : letI := (bialgebra e).toCoalgebra
        ∀ (f : Module.Dual k B) (w : B), w ∈ V → rightAct f w ∈ V)
      (C : Matrix (Fin d) n k),
      Intertwines ρ (regularRepresentation e (Field.toIsField k) V b hV) C ∧
        ∑ l, (C *ᵥ v) l • (b l : B) = (1 : B) := by
  classical
  let := (bialgebra e).toCoalgebra
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := Function.ne_iff.mp hv0
  let a := normalizedCoefficientFamily e ρ v i
  let S : Finset B := Finset.univ.image a
  let V := regularSpan (K := k) S
  let b := Module.finBasis k V
  have ha : ∀ j, a j ∈ V := by
    intro j
    exact subset_regularSpan S (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  have hV : ∀ (f : Module.Dual k B) (w : B), w ∈ V → rightAct f w ∈ V :=
    fun f _ hw => rightAct_mem_regularSpan S f hw
  let C := coactionCoordinates V b a
  refine ⟨V, Module.finrank k V, b, hV, C, ?_, ?_⟩
  · apply intertwines_of_universalMatrix e
    rw [regularRepresentation_universalMatrix]
    exact coactionCoordinates_mul V b a (Unipotent.universalMatrix e ρ) ha
      (normalizedCoefficientFamily_comul e ρ v i)
  · calc
      _ = ∑ j, v j • ∑ l, extendedCoord V b l (a j) • (b l : B) := by
        simp only [C, coactionCoordinates, Matrix.mulVec, dotProduct,
          Matrix.of_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun l _ => by rw [mul_comm]
      _ = ∑ j, v j • a j := by
        exact Finset.sum_congr rfl fun j _ => by rw [basis_expand V b (ha j)]
      _ = 1 := normalizedCoefficientFamily_fixed e ρ v hv i hi

end Langlands.GroupScheme.Chevalley
