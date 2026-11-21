import Langlands.TraceFormula.GeneralLinearCuspFormLocalVanishingStatement
import Langlands.Representation.Shahidi.TwoBlocks

/-! Matrix-coordinate change of variables for the local cusp-form condition. -/

noncomputable section

open MeasureTheory
open Langlands.GeneralLinear Langlands.Global Langlands.Shahidi

namespace Langlands.TraceFormula

universe u

section TwoBlockCoordinates

variable {R : Type*} [CommRing R] {a b : ℕ}

private theorem blockUnipotent_entry (Z : Matrix (Fin a) (Fin b) R) (i j : Fin (a + b)) :
    blockUnipotent rfl Z i j = Matrix.fromBlocks 1 Z 0 1
      (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) := by
  rw [blockUnipotent_val]
  simp [Matrix.reindex_apply]

private theorem blockUnipotent_mem_twoBlocks (ha : 0 < a) (hb : 0 < b)
    (Z : Matrix (Fin a) (Fin b) R) :
    blockUnipotent rfl Z ∈ (twoBlocks a b ha hb).unipotentSubgroup R := by
  rw [BlockShape.mem_unipotentSubgroup_iff, twoBlocks_mem_parabolic_iff]
  refine ⟨fun i j => ?_, ?_⟩
  · simp [blockUnipotent_entry]
  · intro i
    fin_cases i
    · change ∀ j k : Fin a, blockUnipotent rfl Z ((twoBlocks a b ha hb).index 0 j)
        ((twoBlocks a b ha hb).index 0 k) = if j = k then 1 else 0
      intro j k
      rw [twoBlocks_index_first ha hb j, twoBlocks_index_first ha hb k]
      simp [blockUnipotent_entry, Matrix.one_apply]
    · change ∀ j k : Fin b, blockUnipotent rfl Z ((twoBlocks a b ha hb).index 1 j)
        ((twoBlocks a b ha hb).index 1 k) = if j = k then 1 else 0
      intro j k
      rw [twoBlocks_index_second ha hb j, twoBlocks_index_second ha hb k]
      simp [blockUnipotent_entry, Matrix.one_apply]

private def twoBlockUnipotentEquiv [TopologicalSpace R] [IsTopologicalRing R]
    (ha : 0 < a) (hb : 0 < b) :
    Multiplicative (Matrix (Fin a) (Fin b) R) ≃ₜ* (twoBlocks a b ha hb).unipotentSubgroup R where
  toFun Z := ⟨blockUnipotent rfl Z.toAdd, blockUnipotent_mem_twoBlocks ha hb Z.toAdd⟩
  invFun g := Multiplicative.ofAdd (g.val.val.submatrix (Fin.castAdd b) (Fin.natAdd a))
  left_inv Z := by
    change (blockUnipotent rfl Z.toAdd).val.submatrix (Fin.castAdd b) (Fin.natAdd a) = Z.toAdd
    apply Matrix.ext
    intro i j
    change blockUnipotent rfl Z.toAdd (i.castAdd b) (j.natAdd a) = Z.toAdd i j
    simp [blockUnipotent_entry]
  right_inv g := by
    apply Subtype.ext
    apply Units.ext
    apply Matrix.ext
    intro i j
    change blockUnipotent rfl (g.val.val.submatrix (Fin.castAdd b) (Fin.natAdd a)) i j = g.val i j
    obtain ⟨hlower, hdiag⟩ := (BlockShape.mem_unipotentSubgroup_iff _ _ _).mp g.property
    induction i using Fin.addCases <;> induction j using Fin.addCases
    · rename_i i j
      have h := hdiag 0 i j
      rw [twoBlocks_index_first ha hb i, twoBlocks_index_first ha hb j] at h
      simpa [blockUnipotent_entry, Matrix.one_apply] using! h.symm
    · simp [blockUnipotent_entry]
    · rename_i i j
      simpa [blockUnipotent_entry] using ((twoBlocks_mem_parabolic_iff ha hb R g.val).mp hlower i j).symm
    · rename_i i j
      have h := hdiag 1 i j
      rw [twoBlocks_index_second ha hb i, twoBlocks_index_second ha hb j] at h
      simpa [blockUnipotent_entry, Matrix.one_apply] using! h.symm
  map_mul' Z W := Subtype.ext (blockUnipotent_add rfl Z.toAdd W.toAdd)
  continuous_toFun :=
    ((continuous_blockUnipotent rfl).comp continuous_toAdd).subtype_mk _
  continuous_invFun := continuous_ofAdd.comp <|
    (Units.continuous_val.comp continuous_subtype_val).matrix_submatrix _ _

end TwoBlockCoordinates

/-- Vanishing of local constant terms gives vanishing of each two-block matrix integral. -/
theorem generalLinearCuspFormLocalVanishing : GeneralLinearCuspFormLocalVanishingStatement.{u} := by
  intro K _ _ n v f hf a b h ha hb
  subst n
  intro ν hν x y
  let R := FiniteCompletion K v
  let M := Matrix (Fin a) (Fin b) R
  let B := twoBlocks a b ha hb
  let : MeasurableSpace (GeneralLinear (a + b) R) := borel _
  let : BorelSpace (GeneralLinear (a + b) R) := ⟨rfl⟩
  let : MeasurableSpace (Multiplicative M) := borel M
  let : BorelSpace (Multiplicative M) := ⟨rfl⟩
  let νmul : Measure (Multiplicative M) := ν
  let : νmul.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hν.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hν.toIsOpenPosMeasure
      map_mul_left_eq_self := fun z => hν.map_add_left_eq_self z.toAdd }
  let e := twoBlockUnipotentEquiv (R := R) ha hb
  let μ : Measure (B.unipotentSubgroup R) := νmul.map e
  have hμ : μ.IsHaarMeasure := e.isHaarMeasure_map νmul
  let φ : GeneralLinear (a + b) R → ℂ := fun g =>
    f (x * AdelicGL.ofFinite K (a + b) (FiniteAdelicGL.localInclusion K (a + b) v g) * y)
  have hzero : (∫ g : B.unipotentSubgroup R, φ g.val ∂μ) = 0 := by
    simpa only [one_mul, mul_one] using ((hf x y B (Nat.le_refl 2) μ hμ).2 1 1)
  exact (integral_map_equiv (μ := νmul) e.toHomeomorph.toMeasurableEquiv
    (fun g : B.unipotentSubgroup R => φ g.val)).symm.trans hzero

end Langlands.TraceFormula
