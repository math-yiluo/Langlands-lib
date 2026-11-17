import Langlands.Global.RankinSelberg.AdelicCorrectionDenominator

/-! # Archimedean bounds for actual diagonal corrections -/

noncomputable section
universe u
open NumberField
open scoped Classical Matrix.Norms.Elementwise
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open PrimitiveAdelicHeight Langlands.GeneralLinear.RectangularIwasawa

variable (F : Type u) [Field F] [NumberField F]

/-- Regard an idelic diagonal tuple as an additive adelic row. -/
def diagonalIdeleRow {n : ℕ} (c : Fin n → Ideles F) : RowVector F n :=
  fun _ i => (c i : Adeles F)

/-- The actual ring projection from full adeles to mixed archimedean
coordinates. -/
def archimedeanAdeleProjection : Adeles F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

private theorem mapped_norm_bounded_correction
    {𝕜 : Type*} [NormedField 𝕜] (f : Adeles F →+* 𝕜)
    {a d : ℕ} (x : Matrix (Fin d) (Fin a) (Adeles F))
    (U K : AdelicGL F (a + d + 1)) (c : Fin (a + d + 1) → Ideles F)
    (hU : IsUnitriangular U.val)
    (hK : ∀ i j, ‖f (K i j)‖ ≤ 1) (hKi : ∀ i j, ‖f (K⁻¹ i j)‖ ≤ 1)
    (hfac : GeneralLinear.lowerBlockLocalization 1 1 x 1 = U * diagonalGL c * K)
    (C : ℝ) (hC : 1 ≤ C) (hx : ∀ i j, ‖f (x i j)‖ ≤ C) :
    IsNormBoundedUnitTuple (fun q => Units.map f.toMonoidHom (c q))
      (((a + d + 1 : ℕ) : ℝ) * C) := by
  have hlocal :
      GeneralLinear.lowerBlockPair 1 ((extendRectangle 1 x).map f) 1 =
        Matrix.GeneralLinearGroup.map f U *
          diagonalGL (fun q => Units.map f.toMonoidHom (c q)) *
            Matrix.GeneralLinearGroup.map f K := by
    have hh := congrArg (Matrix.GeneralLinearGroup.map f) hfac
    rw [lowerBlockLocalization_one_eq_pair,
      map_lowerBlockPair_one f 1 (extendRectangle 1 x),
      map_mul, map_mul, map_diagonalGL_units, map_one] at hh
    exact hh
  have hki : ∀ i j, ‖(Matrix.GeneralLinearGroup.map f K)⁻¹ i j‖ ≤ 1 := by
    intro i j
    rw [← map_inv]
    exact hKi i j
  have hxx : ∀ i j, ‖((extendRectangle 1 x).map f) i j‖ ≤ C := by
    intro i j
    induction i using Fin.addCases with
    | left i =>
      simp only [Matrix.map_apply, extendRectangle, Fin.append_left]
      exact hx i j
    | right i =>
      simp only [Matrix.map_apply, extendRectangle, Fin.append_right, Pi.zero_apply,
        map_zero, norm_zero]
      exact zero_le_one.trans hC
  have hh := norm_bounded_diagonal_correction ((extendRectangle 1 x).map f)
    (Matrix.GeneralLinearGroup.map f U) (Matrix.GeneralLinearGroup.map f K)
    (fun q => Units.map f.toMonoidHom (c q)) (hU.map f)
    hK hki hlocal C hC hxx
  intro q
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hh q

private theorem real_standardCompact_entry {n : ℕ}
    (K : AdelicGL F n) (hK : K ∈ standardCompact F n)
    (v : {v : InfinitePlace F // v.IsReal}) (i j : Fin n) :
    ‖realCoord v (archimedeanAdeleProjection F (K i j))‖ ≤ 1 := by
  have hu := ((mem_standardInfiniteCompact_iff F n _).mp
    ((mem_standardCompact_iff F n K).mp hK).1).1 v
  exact Langlands.LinearAlgebra.TriangularUnitary.norm_le_one_of_mem_unitaryGroup hu i j

private theorem complex_standardCompact_entry {n : ℕ}
    (K : AdelicGL F n) (hK : K ∈ standardCompact F n)
    (v : {v : InfinitePlace F // v.IsComplex}) (i j : Fin n) :
    ‖complexCoord v (archimedeanAdeleProjection F (K i j))‖ ≤ 1 := by
  have hu := ((mem_standardInfiniteCompact_iff F n _).mp
    ((mem_standardCompact_iff F n K).mp hK).1).2 v
  exact Langlands.LinearAlgebra.TriangularUnitary.norm_le_one_of_mem_unitaryGroup hu i j

/-- The actual correction and its inverse have at most linear
archimedean growth in the rectangular coordinate. -/
theorem diagonal_correction_archimedean_norm_le
    {a d : ℕ} (x : Matrix (Fin d) (Fin a) (Adeles F))
    (U K : AdelicGL F (a + d + 1)) (c : Fin (a + d + 1) → Ideles F)
    (hU : IsUnitriangular U.val) (hK : K ∈ standardCompact F (a + d + 1))
    (hfac : GeneralLinear.lowerBlockLocalization 1 1 x 1 = U * diagonalGL c * K) :
    ‖archimedeanCoordinates F (a + d + 1) (diagonalIdeleRow F c)‖ ≤
        ((a + d + 1 : ℕ) : ℝ) * (1 + ‖rectangleArchimedeanCoordinates F d a x‖) ∧
      ‖archimedeanCoordinates F (a + d + 1) (diagonalIdeleRow F (fun q => (c q)⁻¹))‖ ≤
        ((a + d + 1 : ℕ) : ℝ) * (1 + ‖rectangleArchimedeanCoordinates F d a x‖) := by
  let X := rectangleArchimedeanCoordinates F d a x
  let C : ℝ := 1 + ‖X‖
  let H : ℝ := ((a + d + 1 : ℕ) : ℝ) * C
  have hC : 1 ≤ C := by dsimp [C]; linarith [norm_nonneg X]
  have hH : 0 ≤ H := mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hC)
  have hKi := (standardCompact F _).inv_mem hK
  have hr (v : {v : InfinitePlace F // v.IsReal}) :
      IsNormBoundedUnitTuple
        (fun q => Units.map ((realCoord v).comp (archimedeanAdeleProjection F)).toMonoidHom (c q))
        H := by
    apply mapped_norm_bounded_correction F ((realCoord v).comp (archimedeanAdeleProjection F))
      x U K c hU (real_standardCompact_entry F K hK v)
      (real_standardCompact_entry F K⁻¹ hKi v) hfac C hC
    intro i j
    have hh : ‖(X i j).1 v‖ ≤ ‖X‖ :=
      (norm_le_pi_norm (X i j).1 v).trans
        ((norm_fst_le (X i j)).trans (Matrix.norm_entry_le_entrywise_sup_norm X))
    exact hh.trans (by dsimp [C]; linarith)
  have hc (v : {v : InfinitePlace F // v.IsComplex}) :
      IsNormBoundedUnitTuple
        (fun q => Units.map ((complexCoord v).comp (archimedeanAdeleProjection F)).toMonoidHom (c q))
        H := by
    apply mapped_norm_bounded_correction F ((complexCoord v).comp (archimedeanAdeleProjection F))
      x U K c hU (complex_standardCompact_entry F K hK v)
      (complex_standardCompact_entry F K⁻¹ hKi v) hfac C hC
    intro i j
    have hh : ‖(X i j).2 v‖ ≤ ‖X‖ :=
      (norm_le_pi_norm (X i j).2 v).trans
        ((norm_snd_le (X i j)).trans (Matrix.norm_entry_le_entrywise_sup_norm X))
    exact hh.trans (by dsimp [C]; linarith)
  constructor
  · apply (pi_norm_le_iff_of_nonneg hH).mpr
    intro q
    rw [Prod.norm_def, max_le_iff]
    exact ⟨(pi_norm_le_iff_of_nonneg hH).mpr (fun v => (hr v q).1),
      (pi_norm_le_iff_of_nonneg hH).mpr (fun v => (hc v q).1)⟩
  · apply (pi_norm_le_iff_of_nonneg hH).mpr
    intro q
    rw [Prod.norm_def, max_le_iff]
    exact ⟨(pi_norm_le_iff_of_nonneg hH).mpr (fun v => (hr v q).2),
      (pi_norm_le_iff_of_nonneg hH).mpr (fun v => (hc v q).2)⟩

end Langlands.Global.RankinSelbergGlobal
