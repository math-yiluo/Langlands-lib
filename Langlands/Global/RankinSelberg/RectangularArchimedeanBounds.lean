import Langlands.Global.RankinSelberg.RectangularFiniteDenominator
import Mathlib.Analysis.Matrix.Normed

/-! # Archimedean polynomial bounds for adelic rectangles -/

noncomputable section
universe u
open NumberField
open scoped Classical Matrix.Norms.Elementwise
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open PrimitiveAdelicHeight Langlands.GeneralLinear.RectangularIwasawa

variable (F : Type u) [Field F] [NumberField F]

/-- The archimedean mixed coordinates of every rectangular entry. -/
def rectangleArchimedeanCoordinates (d a : ℕ)
    (x : Matrix (Fin d) (Fin a) (Adeles F)) :
    Matrix (Fin d) (Fin a) (mixedEmbedding.mixedSpace F) :=
  fun i j => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i j).1

private def archProjection : Adeles F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

private theorem project_units_div {R : Type*} [CommRing R] {𝕜 : Type*} [Field 𝕜]
    (f : R →+* 𝕜) (b c : Rˣ) :
    f ((b / c : Rˣ) : R) = f (b : R) / f (c : R) := by
  change ((Units.map f.toMonoidHom (b / c) : 𝕜ˣ) : 𝕜) = _
  rw [map_div, Units.val_div_eq_div_val]
  rfl

private theorem projected_coordinate_le
    {𝕜 : Type*} [NormedField 𝕜] (f : Adeles F →+* 𝕜)
    {a d : ℕ} (g : AdelicGL F a)
    (x : Matrix (Fin d) (Fin a) (Adeles F))
    (U K : AdelicGL F (a + d + 1)) (c : Fin (a + d + 1) → Ideles F)
    (hU : IsUnitriangular U.val)
    (hK : ∀ i j, ‖f (K i j)‖ ≤ 1) (hKi : ∀ i j, ‖f (K⁻¹ i j)‖ ≤ 1)
    (hfac : GeneralLinear.lowerBlockLocalization 1 g x 1 = U * diagonalGL c * K)
    (R : ℝ) (hR : 1 ≤ R)
    (hroot : ∀ q : Fin (a + d),
      ‖f ((c q.castSucc / c q.succ : Ideles F) : Adeles F)‖ ≤ R)
    (i : Fin d) (j : Fin a) :
    ‖f (x i j)‖ ≤ rectangularSupportRadius d R * ((d + 1).factorial : ℝ) := by
  let B := Matrix.GeneralLinearGroup.map f (U * diagonalGL c)
  let k := Matrix.GeneralLinearGroup.map f K
  let gx := Matrix.GeneralLinearGroup.map f g
  let xx := x.map f
  have hB : B.val.IsUpperTriangular := by
    change ((U.val * (diagonalGL c).val).map f).IsUpperTriangular
    exact (hU.1.mul (Matrix.blockTriangular_diagonal _)).map f
  have hdiag (q : Fin (a + d + 1)) : B q q = f (c q : Adeles F) := by
    change f ((U.val * (diagonalGL c).val) q q) = _
    rw [diagonalGL, Matrix.mul_diagonal, hU.2 q, one_mul]
  have hk : ∀ p q, ‖k p q‖ ≤ 1 := hK
  have hki : ∀ p q, ‖k⁻¹ p q‖ ≤ 1 := by
    intro p q
    dsimp only [k]
    rw [← map_inv]
    exact hKi p q
  have hlocal : GeneralLinear.lowerBlockLocalization 1 gx xx 1 = B * k := by
    have hh := congrArg (Matrix.GeneralLinearGroup.map f) hfac
    rw [map_lowerBlockLocalization_one f, map_mul] at hh
    exact hh
  have hr (q : Fin d) :
      ‖B (q.castSucc.natAdd a) (q.castSucc.natAdd a) /
        B (q.succ.natAdd a) (q.succ.natAdd a)‖ ≤ R := by
    rw [hdiag, hdiag, ← project_units_div]
    have hleft : (q.natAdd a : Fin (a + d)).castSucc = q.castSucc.natAdd a := by
      apply Fin.ext
      rfl
    have hright : (q.natAdd a : Fin (a + d)).succ = q.succ.natAdd a := by
      apply Fin.ext
      simp [Nat.add_assoc]
    simpa only [hleft, hright] using hroot (q.natAdd a)
  exact norm_lowerBlockLocalization_coordinate_le_of_roots gx xx B k hB hk hki hlocal R hR hr i j

private theorem real_projection_norm_le_one {n : ℕ}
    (K : AdelicGL F n) (hK : K ∈ standardCompact F n)
    (v : {v : InfinitePlace F // v.IsReal}) (i j : Fin n) :
    ‖realCoord v (archProjection F (K i j))‖ ≤ 1 := by
  have hk := ((mem_standardCompact_iff F n K).mp hK).1
  have hu := ((mem_standardInfiniteCompact_iff F n _).mp hk).1 v
  exact Langlands.LinearAlgebra.TriangularUnitary.norm_le_one_of_mem_unitaryGroup hu i j

private theorem complex_projection_norm_le_one {n : ℕ}
    (K : AdelicGL F n) (hK : K ∈ standardCompact F n)
    (v : {v : InfinitePlace F // v.IsComplex}) (i j : Fin n) :
    ‖complexCoord v (archProjection F (K i j))‖ ≤ 1 := by
  have hk := ((mem_standardCompact_iff F n K).mp hK).1
  have hu := ((mem_standardInfiniteCompact_iff F n _).mp hk).2 v
  exact Langlands.LinearAlgebra.TriangularUnitary.norm_le_one_of_mem_unitaryGroup hu i j

/-- The norm of the whole archimedean rectangle is polynomially bounded
by the archimedean norm of the actual simple-root row. -/
theorem rectangleArchimedeanCoordinates_norm_le
    {a d : ℕ} (g : AdelicGL F a)
    (x : Matrix (Fin d) (Fin a) (Adeles F))
    (U K : AdelicGL F (a + d + 1)) (c : Fin (a + d + 1) → Ideles F)
    (hU : IsUnitriangular U.val) (hK : K ∈ standardCompact F (a + d + 1))
    (hfac : GeneralLinear.lowerBlockLocalization 1 g x 1 = U * diagonalGL c * K) :
    ‖rectangleArchimedeanCoordinates F d a x‖ ≤
      rectangularSupportRadius d
        (1 + ‖archimedeanCoordinates F (a + d) (gaugeSimpleRootRow F (a + d) c)‖) *
          ((d + 1).factorial : ℝ) := by
  let Y := archimedeanCoordinates F (a + d) (gaugeSimpleRootRow F (a + d) c)
  let R : ℝ := 1 + ‖Y‖
  let H : ℝ := rectangularSupportRadius d R * ((d + 1).factorial : ℝ)
  have hR : 1 ≤ R := by dsimp [R]; linarith [norm_nonneg Y]
  have hH : 0 ≤ H := by
    dsimp [H, rectangularSupportRadius]
    positivity
  have hKi := (standardCompact F _).inv_mem hK
  have hreal (i : Fin d) (j : Fin a) (v : {v : InfinitePlace F // v.IsReal}) :
      ‖(rectangleArchimedeanCoordinates F d a x i j).1 v‖ ≤ H := by
    apply projected_coordinate_le F ((realCoord v).comp (archProjection F))
      g x U K c hU (real_projection_norm_le_one F K hK v)
      (real_projection_norm_le_one F K⁻¹ hKi v) hfac R hR ?_ i j
    intro q
    have hh : ‖(Y q).1 v‖ ≤ ‖Y‖ :=
      (norm_le_pi_norm (Y q).1 v).trans
        ((norm_fst_le (Y q)).trans (norm_le_pi_norm Y q))
    exact hh.trans (by dsimp [R]; linarith)
  have hcomplex (i : Fin d) (j : Fin a) (v : {v : InfinitePlace F // v.IsComplex}) :
      ‖(rectangleArchimedeanCoordinates F d a x i j).2 v‖ ≤ H := by
    apply projected_coordinate_le F ((complexCoord v).comp (archProjection F))
      g x U K c hU (complex_projection_norm_le_one F K hK v)
      (complex_projection_norm_le_one F K⁻¹ hKi v) hfac R hR ?_ i j
    intro q
    have hh : ‖(Y q).2 v‖ ≤ ‖Y‖ :=
      (norm_le_pi_norm (Y q).2 v).trans
        ((norm_snd_le (Y q)).trans (norm_le_pi_norm Y q))
    exact hh.trans (by dsimp [R]; linarith)
  apply (pi_norm_le_iff_of_nonneg hH).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg hH).mpr
  intro j
  rw [Prod.norm_def, max_le_iff]
  exact ⟨(pi_norm_le_iff_of_nonneg hH).mpr (hreal i j),
    (pi_norm_le_iff_of_nonneg hH).mpr (hcomplex i j)⟩

end Langlands.Global.RankinSelbergGlobal
