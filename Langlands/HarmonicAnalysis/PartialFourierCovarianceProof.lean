import Langlands.HarmonicAnalysis.PartialFourierCovarianceStatement
import Langlands.HarmonicAnalysis.RectangularFourierCovarianceProof
import Langlands.HarmonicAnalysis.SelfDualSigmaFiniteProof
import Langlands.HarmonicAnalysis.FiniteProductMeasureScaling
import Mathlib.MeasureTheory.Group.Integral

/-! Covariance of the transported action `rectangularRho0` under `diag(h, 1)`, the
upper last-column unipotent matrices and `diag(1, …, 1, a)`. Each law comes from an
identity between the chosen last-column transform and right translation, proved by a
translation or a coordinate scaling of the supplied product measure `rowMeasure μ n`. -/

noncomputable section

open MeasureTheory
open scoped BigOperators NNReal ENNReal Pointwise

namespace Langlands.HarmonicAnalysis

universe uK

section Matrices

variable {K : Type uK} [Field K] {n : ℕ}

/-- Entries of `[x,u] M`, split into the first `n` rows of `M` and its last row. -/
theorem rectangularJoin_mul_apply (x : Matrix (Fin n) (Fin n) K) (u : Fin n → K)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (i : Fin n) (j : Fin (n + 1)) :
    (rectangularJoin x u * M) i j =
      ∑ k : Fin n, x i k * M k.castSucc j + u i * M (Fin.last n) j := by
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp only [rectangularJoin_castSucc, rectangularJoin_last]

private theorem blockSum_castSucc_castSucc (g : Langlands.GeneralLinear n K)
    (h : Langlands.GeneralLinear 1 K) (k j : Fin n) :
    (Langlands.GeneralLinear.blockSum (g, h)).val k.castSucc j.castSucc = g.val k j :=
  Langlands.GeneralLinear.blockSum_apply_left g h k j

private theorem blockSum_castSucc_last (g : Langlands.GeneralLinear n K)
    (h : Langlands.GeneralLinear 1 K) (k : Fin n) :
    (Langlands.GeneralLinear.blockSum (g, h)).val k.castSucc (Fin.last n) = 0 :=
  Langlands.GeneralLinear.blockSum_apply_left_right g h k 0

private theorem blockSum_last_castSucc (g : Langlands.GeneralLinear n K)
    (h : Langlands.GeneralLinear 1 K) (j : Fin n) :
    (Langlands.GeneralLinear.blockSum (g, h)).val (Fin.last n) j.castSucc = 0 :=
  Langlands.GeneralLinear.blockSum_apply_right_left g h 0 j

private theorem blockSum_last_last (g : Langlands.GeneralLinear n K)
    (h : Langlands.GeneralLinear 1 K) :
    (Langlands.GeneralLinear.blockSum (g, h)).val (Fin.last n) (Fin.last n) = h.val 0 0 :=
  Langlands.GeneralLinear.blockSum_apply_right g h 0 0

/-- Right multiplication by `diag(h, 1)` multiplies the square block by `h` and keeps
the last column. -/
theorem rectangularJoin_mul_rankInclusion (h : Langlands.GeneralLinear n K)
    (x : Matrix (Fin n) (Fin n) K) (u : Fin n → K) :
    rectangularJoin x u * (Langlands.GeneralLinear.rankInclusion 1 h).val =
      rectangularJoin (x * h.val) u := by
  change rectangularJoin x u * (Langlands.GeneralLinear.blockSum (h, 1)).val = _
  ext i j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [rectangularJoin_mul_apply, blockSum_castSucc_last, blockSum_last_last]
  · rw [rectangularJoin_mul_apply]
    simp [blockSum_castSucc_castSucc, blockSum_last_castSucc, Matrix.mul_apply]

/-- Right multiplication by `diag(1, …, 1, a)` multiplies the last column by `a`. -/
theorem rectangularJoin_mul_lastScalar (a : Kˣ)
    (x : Matrix (Fin n) (Fin n) K) (u : Fin n → K) :
    rectangularJoin x u * (Langlands.GeneralLinear.blockSum
        ((1 : Langlands.GeneralLinear n K), Langlands.GeneralLinear.scalar (n := 1) a)).val =
      rectangularJoin x (fun i => (a : K) * u i) := by
  ext i j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [rectangularJoin_mul_apply, blockSum_castSucc_last, blockSum_last_last,
      Matrix.GeneralLinearGroup.coe_scalar, mul_comm]
  · simp [rectangularJoin_mul_apply, blockSum_castSucc_castSucc, blockSum_last_castSucc,
      Matrix.one_apply]

/-- The inverse of `diag(1, …, 1, a)` is `diag(1, …, 1, a⁻¹)`. -/
theorem blockSum_lastScalar_inv (a : Kˣ) :
    (Langlands.GeneralLinear.blockSum
        ((1 : Langlands.GeneralLinear n K), Langlands.GeneralLinear.scalar (n := 1) a))⁻¹ =
      Langlands.GeneralLinear.blockSum
        ((1 : Langlands.GeneralLinear n K), Langlands.GeneralLinear.scalar (n := 1) a⁻¹) := by
  rw [← map_inv, Prod.inv_mk, inv_one, map_inv]

private theorem blockUnipotent_entry (v : Fin n → K) (k j : Fin (n + 1)) :
    (Langlands.GeneralLinear.blockUnipotent (a := n) (b := 1) (n := n + 1) rfl
        (fun i _ => v i)).val k j =
      Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) K)
        (fun i (_ : Fin 1) => v i) 0 1 (finSumFinEquiv.symm k) (finSumFinEquiv.symm j) :=
  rfl

private theorem blockUnipotent_castSucc_castSucc (v : Fin n → K) (k j : Fin n) :
    (Langlands.GeneralLinear.blockUnipotent (a := n) (b := 1) (n := n + 1) rfl
        (fun i _ => v i)).val k.castSucc j.castSucc = (1 : Matrix (Fin n) (Fin n) K) k j := by
  rw [blockUnipotent_entry, finSumFinEquiv_symm_apply_castSucc,
    finSumFinEquiv_symm_apply_castSucc]
  rfl

private theorem blockUnipotent_castSucc_last (v : Fin n → K) (k : Fin n) :
    (Langlands.GeneralLinear.blockUnipotent (a := n) (b := 1) (n := n + 1) rfl
        (fun i _ => v i)).val k.castSucc (Fin.last n) = v k := by
  rw [blockUnipotent_entry, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]
  rfl

private theorem blockUnipotent_last_castSucc (v : Fin n → K) (j : Fin n) :
    (Langlands.GeneralLinear.blockUnipotent (a := n) (b := 1) (n := n + 1) rfl
        (fun i _ => v i)).val (Fin.last n) j.castSucc = 0 := by
  rw [blockUnipotent_entry, finSumFinEquiv_symm_last, finSumFinEquiv_symm_apply_castSucc]
  rfl

private theorem blockUnipotent_last_last (v : Fin n → K) :
    (Langlands.GeneralLinear.blockUnipotent (a := n) (b := 1) (n := n + 1) rfl
        (fun i _ => v i)).val (Fin.last n) (Fin.last n) = 1 := by
  rw [blockUnipotent_entry, finSumFinEquiv_symm_last]
  rfl

/-- Right multiplication by `[[I_n, v], [0, 1]]` adds `x v` to the last column. -/
theorem rectangularJoin_mul_blockUnipotent (v : Fin n → K)
    (x : Matrix (Fin n) (Fin n) K) (u : Fin n → K) :
    rectangularJoin x u * (Langlands.GeneralLinear.blockUnipotent (a := n) (b := 1)
        (n := n + 1) rfl (fun i _ => v i)).val =
      rectangularJoin x (Matrix.mulVec x v + u) := by
  ext i j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [rectangularJoin_mul_apply]
    simp [blockUnipotent_castSucc_last, blockUnipotent_last_last, Matrix.mulVec, dotProduct]
  · rw [rectangularJoin_mul_apply]
    simp [blockUnipotent_castSucc_castSucc, blockUnipotent_last_castSucc, Matrix.one_apply]

end Matrices

section RowMeasure

variable {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K] [LocallyCompactSpace K]

/-- Coordinatewise multiplication by `a` pushes the supplied product measure forward to
`Δ(a)^(-n)` times itself. -/
theorem rowMeasure_map_mul_left (μ : AdditiveHaarMeasure K) [SigmaFinite μ.measure]
    (n : ℕ) (a : Kˣ) :
    (rowMeasure μ n).map (fun w i => (a : K) * w i) =
      ((distribHaarChar K a)⁻¹ ^ n) • rowMeasure μ n := by
  have hmap := map_mul_left_eq_inv_distribHaarChar μ.measure a
  have hσ : ∀ _ : Fin n, SigmaFinite (μ.measure.map (fun x => (a : K) * x)) := fun _ => by
    rw [hmap]
    infer_instance
  have h := Measure.pi_map_pi (μ := fun _ : Fin n => μ.measure)
    (f := fun (_ : Fin n) (x : K) => (a : K) * x) (hμ := hσ)
    (fun _ => (measurable_const_mul (a : K)).aemeasurable)
  change (Measure.pi fun _ : Fin n => μ.measure).map (fun w i => (a : K) * w i) = _
  rw [h]
  simp only [hmap]
  rw [pi_nnreal_smul, Fin.prod_const]
  rfl

/-- Change of variables for coordinatewise scaling on `rowMeasure μ n`, valid for every
function since the scaling is a measurable equivalence. -/
theorem integral_rowMeasure_mul_left (μ : AdditiveHaarMeasure K) [SigmaFinite μ.measure]
    (n : ℕ) (a : Kˣ) (f : (Fin n → K) → ℂ) :
    ∫ w, f (fun i => (a : K) * w i) ∂rowMeasure μ n =
      (((distribHaarChar K a : ℝ) : ℂ) ^ n)⁻¹ * ∫ w, f w ∂rowMeasure μ n := by
  let e : (Fin n → K) ≃ᵐ (Fin n → K) :=
    MeasurableEquiv.piCongrRight fun _ => MeasurableEquiv.mulLeft₀ (a : K) a.ne_zero
  have he : (e : (Fin n → K) → Fin n → K) = fun w i => (a : K) * w i := rfl
  have h := e.measurableEmbedding.integral_map (μ := rowMeasure μ n) f
  simp only [he] at h
  rw [rowMeasure_map_mul_left, integral_smul_nnreal_measure] at h
  rw [← h, NNReal.smul_def, Complex.real_smul]
  push_cast
  rw [inv_pow]

omit [LocallyCompactSpace K] in
/-- Translation invariance of `rowMeasure μ n`, valid for every function. -/
theorem integral_rowMeasure_add_left (μ : AdditiveHaarMeasure K) [SigmaFinite μ.measure]
    (n : ℕ) (c : Fin n → K) (f : (Fin n → K) → ℂ) :
    ∫ w, f (c + w) ∂rowMeasure μ n = ∫ w, f w ∂rowMeasure μ n := by
  have : (rowMeasure μ n).IsAddLeftInvariant :=
    inferInstanceAs (Measure.pi fun _ : Fin n => μ.measure).IsAddLeftInvariant
  exact integral_add_left_eq_self f c

end RowMeasure

section Transform

variable {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K] [LocallyCompactSpace K] [T2Space K]
  [TotallyDisconnectedSpace K]
  (ψ : UnitaryAdditiveCharacter K) (μ : AdditiveHaarMeasure K) (n : ℕ)
  (hsd : IsSelfDual ψ μ)

omit [TopologicalSpace K] [IsTopologicalRing K] [MeasurableSpace K] [BorelSpace K]
  [LocallyCompactSpace K] [T2Space K] [TotallyDisconnectedSpace K] in
private theorem rowPairing_add_right (y c u : Fin n → K) :
    rowPairing y (c + u) = rowPairing y c + rowPairing y u := by
  simp [rowPairing, mul_add, Finset.sum_add_distrib]

omit [TopologicalSpace K] [IsTopologicalRing K] [MeasurableSpace K] [BorelSpace K]
  [LocallyCompactSpace K] [T2Space K] [TotallyDisconnectedSpace K] in
private theorem rowPairing_inv_mul (a : Kˣ) (y u : Fin n → K) :
    rowPairing (fun i => ((a⁻¹ : Kˣ) : K) * y i) (fun i => (a : K) * u i) =
      rowPairing y u := by
  refine Finset.sum_congr rfl fun i _ => ?_
  calc ((a⁻¹ : Kˣ) : K) * y i * ((a : K) * u i) =
      (((a⁻¹ : Kˣ) : K) * (a : K)) * (y i * u i) := by ring
    _ = y i * u i := by rw [Units.inv_mul, one_mul]

/-- The chosen transform commutes with right translation by `diag(h, 1)`. -/
theorem partialFourierEquiv_translate_rankInclusion (h : Langlands.GeneralLinear n K)
    (F : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K)) :
    partialFourierEquiv ψ μ n hsd
        (rectangularTranslate (Langlands.GeneralLinear.rankInclusion 1 h) F) =
      rectangularTranslate (Langlands.GeneralLinear.rankInclusion 1 h)
        (partialFourierEquiv ψ μ n hsd F) := by
  ext m
  obtain ⟨x, y, rfl⟩ : ∃ x y, rectangularJoin x y = m := ⟨_, _, rectangularJoin_split m⟩
  rw [rectangularTranslate_apply, rectangularJoin_mul_rankInclusion,
    partialFourierEquiv_apply, partialFourierEquiv_apply]
  unfold partialFourierIntegral
  simp only [rectangularFirstColumns_join, rectangularLastColumn_join,
    rectangularTranslate_apply, rectangularJoin_mul_rankInclusion]

/-- Right translation by `[[I_n, v], [0, 1]]` becomes multiplication by `ψ(⟨y, x v⟩)`
after the chosen transform, by translation invariance of `rowMeasure μ n`. -/
theorem partialFourierEquiv_translate_blockUnipotent (v : Fin n → K)
    (F : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K))
    (x : Matrix (Fin n) (Fin n) K) (y : Fin n → K) :
    partialFourierEquiv ψ μ n hsd
        (rectangularTranslate (Langlands.GeneralLinear.blockUnipotent (a := n) (b := 1)
          (n := n + 1) rfl (fun i _ => v i)) F) (rectangularJoin x y) =
      partialFourierEquiv ψ μ n hsd F (rectangularJoin x y) *
        ψ.complex (rowPairing y (Matrix.mulVec x v)) := by
  have : SigmaFinite μ.measure := selfDualSigmaFinite K ψ μ hsd
  rw [partialFourierEquiv_apply, partialFourierEquiv_apply]
  unfold partialFourierIntegral
  simp only [rectangularFirstColumns_join, rectangularLastColumn_join,
    rectangularTranslate_apply, rectangularJoin_mul_blockUnipotent]
  set c := Matrix.mulVec x v
  calc (∫ u, F (rectangularJoin x (c + u)) * ψ.complex (-rowPairing y u) ∂rowMeasure μ n) =
      ∫ u, (fun w => F (rectangularJoin x w) * ψ.complex (-rowPairing y w) *
        ψ.complex (rowPairing y c)) (c + u) ∂rowMeasure μ n := by
        congr 1
        funext u
        have hp : -rowPairing y u = -rowPairing y (c + u) + rowPairing y c := by
          rw [rowPairing_add_right]
          ring
        simp only
        rw [hp, AddChar.map_add_eq_mul, mul_assoc]
    _ = ∫ w, F (rectangularJoin x w) * ψ.complex (-rowPairing y w) *
        ψ.complex (rowPairing y c) ∂rowMeasure μ n :=
      integral_rowMeasure_add_left μ n c (fun w => F (rectangularJoin x w) *
        ψ.complex (-rowPairing y w) * ψ.complex (rowPairing y c))
    _ = _ := integral_mul_const _ _

/-- Right translation by `diag(1, …, 1, a)` becomes `Δ(a)^(-n)` times evaluation at
`[x, a⁻¹ y]` after the chosen transform, by the scaling of `rowMeasure μ n`. -/
theorem partialFourierEquiv_translate_lastScalar (a : Kˣ)
    (F : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K))
    (x : Matrix (Fin n) (Fin n) K) (y : Fin n → K) :
    partialFourierEquiv ψ μ n hsd
        (rectangularTranslate (Langlands.GeneralLinear.blockSum
          ((1 : Langlands.GeneralLinear n K), Langlands.GeneralLinear.scalar (n := 1) a)) F)
        (rectangularJoin x y) =
      (((distribHaarChar K a : ℝ) : ℂ) ^ n)⁻¹ *
        partialFourierEquiv ψ μ n hsd F
          (rectangularJoin x (fun i => ((a⁻¹ : Kˣ) : K) * y i)) := by
  have : SigmaFinite μ.measure := selfDualSigmaFinite K ψ μ hsd
  rw [partialFourierEquiv_apply, partialFourierEquiv_apply]
  unfold partialFourierIntegral
  simp only [rectangularFirstColumns_join, rectangularLastColumn_join,
    rectangularTranslate_apply, rectangularJoin_mul_lastScalar]
  rw [← integral_rowMeasure_mul_left μ n a]
  congr 1
  funext u
  rw [rowPairing_inv_mul]

end Transform

/-- JPSS Section 6.1 formulas (3), (4) and (5) for the transported action
`rectangularRho0`, in the generic Haar-character form of the target statement. -/
theorem partialFourierCovariance : PartialFourierCovarianceStatement.{uK} := by
  intro K _ _ _ _ _ _ _ _ ψ μ n hsd
  refine ⟨fun h Φ => ?_, fun v Φ x y => ?_, fun a Φ => ?_⟩
  · rw [rectangularRho0_apply, partialFourierEquiv_translate_rankInclusion,
      LinearEquiv.apply_symm_apply]
  · rw [rectangularRho0_apply, partialFourierEquiv_translate_blockUnipotent,
      LinearEquiv.apply_symm_apply]
  · ext m
    obtain ⟨x, y, rfl⟩ : ∃ x y, rectangularJoin x y = m := ⟨_, _, rectangularJoin_split m⟩
    rw [rectangularRho0_apply, partialFourierEquiv_translate_lastScalar,
      LinearEquiv.apply_symm_apply]
    change _ = _ * rectangularTranslate _ Φ (rectangularJoin x y)
    rw [rectangularTranslate_apply, blockSum_lastScalar_inv, rectangularJoin_mul_lastScalar]

end Langlands.HarmonicAnalysis
