import Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof
import Langlands.HarmonicAnalysis.RectangularFourier

/-! Compactness of the inner variable in the full-rank part of JPSS (10). -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker Matrix

universe uF uV

section Algebra

variable {K : Type uF} [Field K] {n : ℕ}

/-- The open full-row-rank rectangular locus, expressed by a right inverse. -/
def AdjacentRankFullRank (M : Matrix (Fin n) (Fin (n + 1)) K) : Prop :=
  ∃ R : Matrix (Fin (n + 1)) (Fin n) K, M * R = 1

theorem adjacentRankFullRank_mul_iff
    (M : Matrix (Fin n) (Fin (n + 1)) K) (g : GeneralLinear (n + 1) K) :
    AdjacentRankFullRank (M * g.val) ↔ AdjacentRankFullRank M := by
  constructor
  · rintro ⟨R, hR⟩
    exact ⟨g.val * R, by simpa only [Matrix.mul_assoc] using hR⟩
  · rintro ⟨R, hR⟩
    refine ⟨(g⁻¹).val * R, ?_⟩
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc g.val, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.one_mul, hR]

theorem adjacentRankFullRank_join_zero_iff (A : Matrix (Fin n) (Fin n) K) :
    AdjacentRankFullRank (rectangularJoin A 0) ↔ IsUnit A := by
  constructor
  · rintro ⟨R, hR⟩
    have hmul : A * R.submatrix Fin.castSucc id = 1 := by
      ext i j
      have he := congrFun (congrFun hR i) j
      simpa only [Matrix.mul_apply, Fin.sum_univ_castSucc, rectangularJoin_castSucc,
        rectangularJoin_last, Pi.zero_apply, zero_mul, add_zero, Matrix.submatrix_apply,
        id_eq] using he
    apply (Matrix.isUnit_iff_isUnit_det A).mpr
    have hd := congrArg Matrix.det hmul
    rw [Matrix.det_mul, Matrix.det_one] at hd
    apply Ne.isUnit
    intro hz
    rw [hz, zero_mul] at hd
    exact zero_ne_one hd
  · rintro ⟨g, rfl⟩
    let Ainv : Matrix (Fin n) (Fin n) K := (g⁻¹).val
    refine ⟨(rectangularJoin Ainv.transpose 0).transpose, ?_⟩
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
    simp only [Matrix.transpose_apply, rectangularJoin_castSucc, rectangularJoin_last,
      Pi.zero_apply, zero_mul, add_zero]
    change (g.val * (g⁻¹).val) i j = _
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

end Algebra

section Topology

variable {K : Type uF} [Field K] [TopologicalSpace K]
  [IsTopologicalDivisionRing K] [T2Space K] {n : ℕ}

/-- A compact rectangular test contained in the full-rank locus restricts to a
compactly supported function on the actual inner general linear group. -/
theorem adjacentRankCompactOrbit_hasCompactSupport_one
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K))
    (hΦ : ∀ M ∈ tsupport (Φ : _ → ℂ), AdjacentRankFullRank M) :
    HasCompactSupport (fun h : GeneralLinear n K => Φ (rectangularJoin h.val 0)) := by
  let S : Set (Matrix (Fin n) (Fin n) K) :=
    rectangularFirstColumns ''
      (tsupport (Φ : _ → ℂ) ∩ {M | rectangularLastColumn M = 0})
  have hS : IsCompact S :=
    (Φ.hasCompactSupport.inter_right
      (isClosed_eq continuous_rectangularLastColumn continuous_const)).image
        continuous_rectangularFirstColumns
  have hSinv : S ⊆ Set.range
      (Units.val : GeneralLinear n K → Matrix (Fin n) (Fin n) K) := by
    rintro A ⟨M, ⟨hM, hlast⟩, rfl⟩
    have he : rectangularJoin (rectangularFirstColumns M) 0 = M := by
      rw [← hlast, rectangularJoin_split]
    have hu : IsUnit (rectangularFirstColumns M) :=
      (adjacentRankFullRank_join_zero_iff _).mp (by rw [he]; exact hΦ M hM)
    exact ⟨hu.unit, hu.unit_spec⟩
  have hc : IsCompact
      ((Units.val : GeneralLinear n K → Matrix (Fin n) (Fin n) K) ⁻¹' S) :=
    (isEmbedding_generalLinear_val n).isInducing.isCompact_preimage' hS hSinv
  refine HasCompactSupport.intro hc fun h hh => ?_
  by_contra hn
  apply hh
  exact ⟨rectangularJoin h.val 0,
    ⟨subset_tsupport _ hn, by simp⟩, by simp⟩

omit [T2Space K] in
/-- Full rank is preserved by every rectangular right translate. -/
theorem adjacentRankCompactOrbit_translate
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K))
    (hΦ : ∀ M ∈ tsupport (Φ : _ → ℂ), AdjacentRankFullRank M)
    (g : GeneralLinear (n + 1) K) :
    ∀ M ∈ tsupport (rectangularTranslate g Φ : _ → ℂ), AdjacentRankFullRank M := by
  intro M hM
  have hs : tsupport (rectangularTranslate g Φ : _ → ℂ) =
      (rectangularHomeomorph g) ⁻¹' tsupport (Φ : _ → ℂ) :=
    tsupport_comp_eq_preimage Φ (rectangularHomeomorph g)
  rw [hs] at hM
  exact (adjacentRankFullRank_mul_iff M g).mp (hΦ _ hM)

/-- Compactness in the inner variable of formula (10), for every ambient
right translate and without a growth or twist bound. -/
theorem adjacentRankCompactOrbit_hasCompactSupport
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K))
    (hΦ : ∀ M ∈ tsupport (Φ : _ → ℂ), AdjacentRankFullRank M)
    (g : GeneralLinear (n + 1) K) :
    HasCompactSupport (fun h : GeneralLinear n K =>
      Φ (rectangularJoin h.val 0 * g.val)) :=
  adjacentRankCompactOrbit_hasCompactSupport_one (rectangularTranslate g Φ)
    (adjacentRankCompactOrbit_translate Φ hΦ g)

end Topology

end Langlands.RankinSelberg
