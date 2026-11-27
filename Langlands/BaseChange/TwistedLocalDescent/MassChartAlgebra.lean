import Langlands.BaseChange.TwistedLocalDescent.Iwahori
import Langlands.BaseChange.TwistedLocalDescent.ChartChange

/-! # Group-theoretic form of the twisted chart

The opposite unipotent elements `1 + Z` meet the standard parabolic only in `1`. For a ring
endomorphism `σ` of a nontrivially normed field and `d dinv = 1`, the point `d (1 + χ(X))` of the chart, with
`Z = X_𝔲̄` and `W = X_𝔭`, is the twisted conjugate `(1 + Z)⁻¹ d (1 + W) σ(1 + Z)`. Over an
ultrametric proper nontrivially normed field, for a congruence subgroup `K(r)`, every element
whose matrix is `d (1 + χ(X))` with `‖X‖ ≤ r` is such a twisted conjugate with `‖Z‖ ≤ r` and
`1 + W ∈ P ∩ K(r)`. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.TwistedLocalDescent

open MeasureTheory Measure Set Metric Topology
open Langlands.GeneralLinear
open scoped ENNReal NNReal

universe v

section Algebra

variable {R : Type v} [CommRing R] {n : ℕ} (B : BlockShape n)

theorem add_mem_lowerLevel {t : ℕ} {Y Y' : Matrix (Fin n) (Fin n) R} (hY : Y ∈ lowerLevel B t)
    (hY' : Y' ∈ lowerLevel B t) : Y + Y' ∈ lowerLevel B t := by
  intro a b hab
  rw [Matrix.add_apply] at hab
  by_cases h : Y a b = 0
  · rw [h, zero_add] at hab
    exact hY' a b hab
  · exact hY a b h

theorem neg_mem_lowerLevel {t : ℕ} {Y : Matrix (Fin n) (Fin n) R} (hY : Y ∈ lowerLevel B t) :
    -Y ∈ lowerLevel B t := by
  intro a b hab
  exact hY a b (by simpa using hab)

theorem zero_mem_lowerLevel (t : ℕ) : (0 : Matrix (Fin n) (Fin n) R) ∈ lowerLevel B t := by
  intro a b hab
  exact absurd rfl hab

theorem one_mem_lowerLevel_zero : (1 : Matrix (Fin n) (Fin n) R) ∈ lowerLevel B 0 := by
  intro a b hab
  have : a = b := by
    by_contra h
    exact hab (Matrix.one_apply_ne h)
  subst this
  omega

theorem mem_lowerLevel_zero_of_le {s : ℕ} {Y : Matrix (Fin n) (Fin n) R}
    (hY : Y ∈ lowerLevel B s) : Y ∈ lowerLevel B 0 := by
  intro a b hab
  have := hY a b hab
  omega

theorem pow_mem_lowerLevel_zero {Z : Matrix (Fin n) (Fin n) R} (hZ : Z ∈ lowerLevel B 1) (t : ℕ) :
    Z ^ t ∈ lowerLevel B 0 := by
  cases t with
  | zero => simpa using one_mem_lowerLevel_zero B
  | succ t => exact mem_lowerLevel_zero_of_le B (pow_mem_lowerLevel B hZ t)

theorem lowerInverse_mem_lowerLevel_zero {Z : Matrix (Fin n) (Fin n) R}
    (hZ : ∀ a b, B.coordinateBlock a ≤ B.coordinateBlock b → Z a b = 0) :
    lowerInverse B Z ∈ lowerLevel B 0 := by
  have hZ1 : -Z ∈ lowerLevel B 1 :=
    neg_mem_lowerLevel B (mem_lowerLevel_one_of_mem_lowerLie B hZ)
  unfold lowerInverse
  induction (Finset.range B.length) using Finset.induction_on with
  | empty => simpa using zero_mem_lowerLevel B 0
  | insert t s ht ih =>
    rw [Finset.sum_insert ht]
    exact add_mem_lowerLevel B (pow_mem_lowerLevel_zero B hZ1 t) ih

/-- A block upper triangular matrix which is strictly block lower is zero. -/
theorem eq_zero_of_blockTriangular_of_mem_lowerLevel {Y : Matrix (Fin n) (Fin n) R}
    (hU : Y.BlockTriangular B.coordinateBlock) (hL : Y ∈ lowerLevel B 1) : Y = 0 := by
  ext a b
  by_contra h
  have h1 := hL a b h
  have h2 : B.coordinateBlock b < B.coordinateBlock a := by
    rw [Fin.lt_def]
    omega
  exact h (hU h2)

/-- **`Ū ∩ P = 1`.** -/
theorem lowerUnit_eq_of_mul_inv_mem {𝕂 : Type v} [NormedField 𝕂] (Z Z' : lowerLie (E := 𝕂) B)
    (h : lowerUnit B Z' * (lowerUnit B Z)⁻¹ ∈ B.parabolic 𝕂) : Z' = Z := by
  set g := lowerUnit B Z' * (lowerUnit B Z)⁻¹
  have hg : g.val - 1 = ((Z' : Matrix (Fin n) (Fin n) 𝕂) - Z) * lowerInverse B (Z : Matrix _ _ 𝕂) := by
    change (1 + (Z' : Matrix (Fin n) (Fin n) 𝕂)) * lowerInverse B Z - 1 = _
    have h1 := one_add_mul_lowerInverse B Z.property
    calc (1 + (Z' : Matrix (Fin n) (Fin n) 𝕂)) * lowerInverse B Z - 1 =
        (1 + (Z' : Matrix (Fin n) (Fin n) 𝕂)) * lowerInverse B Z -
          (1 + (Z : Matrix (Fin n) (Fin n) 𝕂)) * lowerInverse B Z := by rw [h1]
      _ = _ := by noncomm_ring
  have hL : g.val - 1 ∈ lowerLevel B 1 := by
    rw [hg]
    have hdiff : (Z' : Matrix (Fin n) (Fin n) 𝕂) - Z ∈ lowerLevel B 1 :=
      mem_lowerLevel_one_of_mem_lowerLie B (sub_mem Z'.property Z.property)
    simpa using mul_mem_lowerLevel B hdiff (lowerInverse_mem_lowerLevel_zero B Z.property)
  have hU : (g.val - 1).BlockTriangular B.coordinateBlock :=
    ((mem_parabolic_iff_blockTriangular B g).mp h).sub Matrix.blockTriangular_one
  have h0 := eq_zero_of_blockTriangular_of_mem_lowerLevel B hU hL
  have hg1 : g = 1 := Units.ext (sub_eq_zero.mp h0)
  have : lowerUnit B Z' = lowerUnit B Z := by
    rw [← mul_inv_eq_one]
    exact hg1
  apply Subtype.ext
  have h2 := congrArg (fun u : GeneralLinear n 𝕂 => u.val) this
  simpa using h2

end Algebra

section Chart

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace matrix_isUltrametricDist
  matrixSupNormedRing matrixSupNormedAlgebra matrix_properSpace

variable {𝕂 : Type v} [NontriviallyNormedField 𝕂] [IsUltrametricDist 𝕂] [ProperSpace 𝕂]
  {n : ℕ} (B : BlockShape n) (σ : 𝕂 →+* 𝕂)

omit [IsUltrametricDist 𝕂] [ProperSpace 𝕂] in
/-- The chart in group form. -/
theorem mul_one_add_twistedChart (d dinv : Matrix (Fin n) (Fin n) 𝕂) (hd : d * dinv = 1)
    (X : Matrix (Fin n) (Fin n) 𝕂) :
    d * (1 + twistedChart B σ d dinv X) =
      lowerInverse B (lowerPart B X) * d * (1 + upperPart B X) * (1 + lowerPart B X).map σ := by
  simp only [twistedChart, add_sub_cancel]
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, hd, one_mul]

omit [IsUltrametricDist 𝕂] [ProperSpace 𝕂] in
theorem val_twistedConj_lowerUnit (d : GeneralLinear n 𝕂) (Z : lowerLie (E := 𝕂) B)
    (h : GeneralLinear n 𝕂) :
    ((lowerUnit B Z)⁻¹ * d * h * Matrix.GeneralLinearGroup.map σ (lowerUnit B Z)).val =
      lowerInverse B (Z : Matrix (Fin n) (Fin n) 𝕂) * d.val * h.val *
        (1 + (Z : Matrix (Fin n) (Fin n) 𝕂)).map σ := rfl

/-- **Elements in the image of the chart are twisted conjugates.** -/
theorem exists_twistedConj_of_mem_chart (d : GeneralLinear n 𝕂)
    (U : OpenSubgroup (GeneralLinear n 𝕂)) {r : ℝ}
    (hrange : Set.range (fun g : U => (g : GeneralLinear n 𝕂).val - 1) =
      closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r)
    {y : GeneralLinear n 𝕂} {X : Matrix (Fin n) (Fin n) 𝕂} (hX : ‖X‖ ≤ r)
    (hy : y.val = d.val * (1 + twistedChart B σ d.val (d⁻¹).val X)) :
    ∃ Z : lowerLie (E := 𝕂) B, ‖(Z : Matrix (Fin n) (Fin n) 𝕂)‖ ≤ r ∧
      ∃ h : B.parabolic 𝕂, (h : GeneralLinear n 𝕂) ∈ U ∧
        y = (lowerUnit B Z)⁻¹ * d * h * Matrix.GeneralLinearGroup.map σ (lowerUnit B Z) := by
  let Z : lowerLie (E := 𝕂) B := ⟨lowerPart B X, lowerPart_mem B X⟩
  have hW : upperPart B X ∈ closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r :=
    mem_closedBall_zero_iff.mpr ((norm_upperPart_le B X).trans hX)
  rw [← hrange] at hW
  obtain ⟨g, hg⟩ := hW
  have hgval : (g : GeneralLinear n 𝕂).val = 1 + upperPart B X := by
    have hg' : (g : GeneralLinear n 𝕂).val - 1 = upperPart B X := hg
    rw [← hg', add_sub_cancel]
  have hgP : (g : GeneralLinear n 𝕂) ∈ B.parabolic 𝕂 := by
    rw [mem_parabolic_iff_blockTriangular, hgval]
    exact (parabolicSubalgebra (R := 𝕂) B).add_mem (parabolicSubalgebra (R := 𝕂) B).one_mem
      (upperPart_mem B X)
  refine ⟨Z, (norm_lowerPart_le B X).trans hX, ⟨g, hgP⟩, g.property, ?_⟩
  apply Units.ext
  rw [hy, val_twistedConj_lowerUnit, mul_one_add_twistedChart B σ _ _ (by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]) X]
  change _ = lowerInverse B (lowerPart B X) * d.val * (g : GeneralLinear n 𝕂).val *
    (1 + lowerPart B X).map σ
  rw [hgval]

end Chart

end Langlands.BaseChange.TwistedLocalDescent
