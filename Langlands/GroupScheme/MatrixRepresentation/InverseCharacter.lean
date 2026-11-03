import Langlands.GroupScheme.MatrixRepresentation.CharacterSpaces
import Langlands.GroupScheme.MatrixRepresentationDual

/-! # Inverse characters in the dual of a character-spanned representation -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj Classical

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]

/-- The coordinate functional on one character summand, written as a dual vector. -/
def characterDualVector (ρ : MatrixRepresentation G n) (χ : rationalCharacters G)
    (j : n) : n → k :=
  (dotProductEquiv k n).symm ((LinearMap.proj j).comp (ρ.characterProjector χ))

theorem characterDualVector_pairing (ρ : MatrixRepresentation G n)
    (χ : rationalCharacters G) (j : n) (v : n → k) :
    ρ.characterDualVector χ j ⬝ᵥ v = ρ.characterProjector χ v j := by
  exact LinearMap.congr_fun ((dotProductEquiv k n).apply_symm_apply _) v

/-- On any character space the pairing selects its specified character. -/
theorem characterDualVector_pairing_of_mem (ρ : MatrixRepresentation G n)
    (χ ψ : rationalCharacters G) (j : n) {v : n → k}
    (hv : v ∈ ρ.characterSpace ψ) :
    ρ.characterDualVector χ j ⬝ᵥ v = if ψ = χ then v j else 0 := by
  rw [characterDualVector_pairing, characterProjector_of_mem ρ χ ψ hv]
  split_ifs <;> rfl

/-- If the character spaces span, the selected functional transforms by its
character under the original action, over every affine test algebra. -/
theorem characterDualVector_pairing_affine (ρ : MatrixRepresentation G n)
    (hspan : (⨆ ψ, ρ.characterSpace ψ) = ⊤)
    (χ : rationalCharacters G) (j : n)
    (A : CommAlgCat.{u} (CommRingCat.of k)) (x : G.affinePoints A) (v : n → k) :
    (fun r => algebraMap k A (ρ.characterDualVector χ j r)) ⬝ᵥ
        ((ρ.affineMatrix A x : Matrix n n A) *ᵥ
          (fun r => algebraMap k A (v r))) =
      (Gm.affineUnitsEquiv (CommRingCat.of k) A (x ≫ χ.toMul.hom.hom) : A) *
        algebraMap k A (ρ.characterDualVector χ j ⬝ᵥ v) := by
  have hv : v ∈ (⨆ ψ, ρ.characterSpace ψ) := by rw [hspan]; trivial
  refine Submodule.iSup_induction ρ.characterSpace
    (motive := fun v => (fun r => algebraMap k A (ρ.characterDualVector χ j r)) ⬝ᵥ
        ((ρ.affineMatrix A x : Matrix n n A) *ᵥ
          (fun r => algebraMap k A (v r))) =
      (Gm.affineUnitsEquiv (CommRingCat.of k) A (x ≫ χ.toMul.hom.hom) : A) *
        algebraMap k A (ρ.characterDualVector χ j ⬝ᵥ v)) hv ?_ ?_ ?_
  · intro ψ v hv
    rw [characterSpace_affine hv, dotProduct_smul]
    have hdot := (algebraMap k A).map_dotProduct (ρ.characterDualVector χ j) v
    change algebraMap k A (ρ.characterDualVector χ j ⬝ᵥ v) =
      (fun r => algebraMap k A (ρ.characterDualVector χ j r)) ⬝ᵥ
        (fun r => algebraMap k A (v r)) at hdot
    rw [← hdot, characterDualVector_pairing_of_mem ρ χ ψ j hv]
    by_cases hψ : ψ = χ
    · subst ψ; simp [smul_eq_mul]
    · simp [hψ]
  · simp [← Pi.zero_def]
  · intro v w hv hw
    simp only [Pi.add_apply, map_add, ← Pi.add_def, Matrix.mulVec_add,
      dotProduct_add, hv, hw, mul_add]

/-- Negating a character inverts its universal unit. -/
theorem characterUnit_neg (χ : rationalCharacters G) :
    CharacterUnits.unit (-χ) = (CharacterUnits.unit χ)⁻¹ := by
  exact congrArg Additive.toMul (map_neg CharacterUnits.unitHom χ)

/-- The selected dual vector has the inverse character when character spaces span. -/
theorem characterDualVector_mem (ρ : MatrixRepresentation G n)
    (hspan : (⨆ ψ, ρ.characterSpace ψ) = ⊤)
    (χ : rationalCharacters G) (j : n) :
    ρ.characterDualVector χ j ∈ ρ.dual.characterSpace (-χ) := by
  rw [mem_characterSpace_iff]
  unfold universalCharacterMatrix
  rw [dual_affineMatrix, GeneralLinear.matrixContragredient_coe]
  funext r
  have h := characterDualVector_pairing_affine ρ hspan χ j
    (CharacterUnits.Coord G) (CharacterUnits.universalPoint G)⁻¹
    (Pi.single r 1 : n → k)
  have hsingle : (fun s => algebraMap k (CharacterUnits.Coord G)
      ((Pi.single r (1 : k) : n → k) s)) =
        (Pi.single r (1 : CharacterUnits.Coord G) : n → CharacterUnits.Coord G) := by
    ext s
    by_cases hs : s = r <;> simp [hs]
  rw [hsingle, map_inv, Matrix.mulVec_single_one, dotProduct_single_one] at h
  have hunit : Gm.affineUnitsEquiv (CommRingCat.of k) (CharacterUnits.Coord G)
      ((CharacterUnits.universalPoint G)⁻¹ ≫ χ.toMul.hom.hom) =
        CharacterUnits.unit (-χ) := by
    rw [GrpObj.inv_comp, map_inv, characterUnit_neg]
    rfl
  rw [hunit, dotProduct_comm] at h
  simpa only [Matrix.mulVec, Matrix.col, Matrix.transpose,
    Pi.smul_apply, smul_eq_mul] using h

/-- A nonzero vector of character `χ` gives a nonzero vector of character `-χ`
in the dual, provided that the original character spaces span. -/
theorem exists_inverse_characterVector (ρ : MatrixRepresentation G n)
    (hspan : (⨆ ψ, ρ.characterSpace ψ) = ⊤)
    (χ : rationalCharacters G) {v : n → k}
    (hv : v ∈ ρ.characterSpace χ) (hne : v ≠ 0) :
    ∃ w : n → k, w ≠ 0 ∧ w ∈ ρ.dual.characterSpace (-χ) := by
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    apply hne
    ext j
    exact (not_not.mp ((not_exists.mp h) j))
  refine ⟨ρ.characterDualVector χ j, ?_, characterDualVector_mem ρ hspan χ j⟩
  intro hw
  have h := characterDualVector_pairing_of_mem ρ χ χ j hv
  apply hj
  simpa [hw] using h.symm

end Langlands.GroupScheme.MatrixRepresentation
