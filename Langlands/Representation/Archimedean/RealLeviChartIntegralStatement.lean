import Langlands.Representation.Archimedean.PrincipalSeriesGramFormula
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Integrability of the Gram bound on the opposite unipotent radical of a parabolic subgroup

Let `Q` be the upper block triangular parabolic subgroup of `GL_N(ℝ)` with diagonal blocks of
sizes `sz_0, …, sz_{c-1}` (`N = ∑ sz_i`). The positions `Fin N` are identified with the pairs
`(i, a)`, `a < sz_i`, in lexicographic order (`finSigmaFinEquiv`); `cls p` is the block of the
position `p`. The opposite unipotent radical `N̄_Q` has the coordinates `X_{pq}` for
`cls q < cls p` (`Coord`), and `n̄(X)` is the identity plus these entries (`lower`).

The statement `RealLeviChartIntegrableStatement` says that `X ↦ ∏_l G_l(n̄(X))^{γ_l}` is
integrable on `N̄_Q`, where `G_l` is the Gram determinant of the rows `l, …, N-1`, provided
`γ_l ≤ -1/2` for every `l ≥ 1` and `γ_l < -1/2` at the first position `l` of every block but the
first. The statement is only stated here.
-/

noncomputable section

open MeasureTheory Matrix

namespace Langlands.Archimedean

set_option autoImplicit false

namespace RealLeviChart

variable {c : ℕ} (sz : Fin c → ℕ)

/-- The block containing the position `p`. -/
def cls (p : Fin (∑ i, sz i)) : Fin c := (finSigmaFinEquiv.symm p).1

/-- The position of the index `a` of the block `i`. -/
def pos (i : Fin c) (a : Fin (sz i)) : Fin (∑ i, sz i) := finSigmaFinEquiv ⟨i, a⟩

/-- The first position of the block `i`, as a natural number. -/
def start (i : ℕ) : ℕ := ∑ k ∈ Finset.range i, if h : k < c then sz ⟨k, h⟩ else 0

theorem cls_pos (i : Fin c) (a : Fin (sz i)) : cls sz (pos sz i a) = i := by
  simp [cls, pos]

theorem pos_cls (p : Fin (∑ i, sz i)) :
    ∃ a : Fin (sz (cls sz p)), pos sz (cls sz p) a = p :=
  ⟨(finSigmaFinEquiv.symm p).2, by simp [cls, pos]⟩

theorem val_pos (i : Fin c) (a : Fin (sz i)) : (pos sz i a : ℕ) = start sz i + a := by
  rw [pos, finSigmaFinEquiv_apply, start]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun k => if h : k < c then sz ⟨k, h⟩ else 0) i]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : (k : ℕ) < c := lt_trans k.2 i.2
  simp only [hk, ↓reduceDIte]
  rfl

theorem start_succ_le {i j : ℕ} (hij : i < j) (hi : i < c) :
    start sz i + sz ⟨i, hi⟩ ≤ start sz j := by
  have h1 : start sz i + sz ⟨i, hi⟩ = start sz (i + 1) := by
    rw [start, start, Finset.sum_range_succ]
    simp only [hi, ↓reduceDIte]
  rw [h1, start, start]
  exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr hij)

/-- Positions in an earlier block come first. -/
theorem lt_of_cls_lt {p q : Fin (∑ i, sz i)} (h : cls sz p < cls sz q) : p < q := by
  obtain ⟨a, ha⟩ := pos_cls sz p
  obtain ⟨b, hb⟩ := pos_cls sz q
  have hp : (p : ℕ) = start sz (cls sz p) + a := by rw [← val_pos, ha]
  have hq : (q : ℕ) = start sz (cls sz q) + b := by rw [← val_pos, hb]
  have hs := start_succ_le sz (Fin.lt_def.mp h) (cls sz p).2
  have e : sz ⟨((cls sz p : Fin c) : ℕ), (cls sz p).2⟩ = sz (cls sz p) := rfl
  rw [e] at hs
  have ha' := a.2
  rw [Fin.lt_def, hp, hq]
  omega

/-- The coordinates of the opposite unipotent radical: the pairs `(p, q)` with
`cls q < cls p`. -/
abbrev Coord := {pq : Fin (∑ i, sz i) × Fin (∑ i, sz i) // cls sz pq.2 < cls sz pq.1}

/-- `n̄(X)`: the identity matrix with the entries `X_{pq}` at the coordinates. -/
def lower (X : Coord sz → ℝ) : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ :=
  Matrix.of fun p q => if h : cls sz q < cls sz p then X ⟨(p, q), h⟩ else if p = q then 1 else 0

theorem lower_isLowerTriangular (X : Coord sz → ℝ) : (lower sz X).IsLowerTriangular := by
  intro p q hpq
  have hpq' : p < q := hpq
  have h1 : ¬ cls sz q < cls sz p := fun h => absurd (lt_of_cls_lt sz h) (lt_asymm hpq')
  simp [lower, h1, hpq'.ne]

theorem lower_apply_self (X : Coord sz → ℝ) (p : Fin (∑ i, sz i)) : lower sz X p p = 1 := by
  simp [lower]

theorem det_lower (X : Coord sz → ℝ) : (lower sz X).det = 1 := by
  rw [det_of_isLowerTriangular _ (lower_isLowerTriangular sz X)]
  simp [lower_apply_self]

/-- `n̄(X)` as an element of `GL_N(ℝ)`. -/
def lowerGL (X : Coord sz → ℝ) : Langlands.GeneralLinear (∑ i, sz i) ℝ :=
  ((Matrix.isUnit_iff_isUnit_det (lower sz X)).mpr (by rw [det_lower]; exact isUnit_one)).unit

theorem lowerGL_val (X : Coord sz → ℝ) :
    ((lowerGL sz X : Langlands.GeneralLinear (∑ i, sz i) ℝ) :
      Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) = lower sz X := rfl

end RealLeviChart

/-- **Statement (integrability of the Gram bound on `N̄_Q`).** Let `Q` be the upper block
triangular parabolic subgroup of `GL_N(ℝ)` with diagonal blocks of sizes `sz_0, …, sz_{c-1}`,
`N = ∑ sz_i`, and let `γ_0, …, γ_{N-1}` be real numbers with `γ_l ≤ -1/2` for `l ≥ 1` and
`γ_l < -1/2` whenever `l` is the first position of a block other than the first one
(`cls (l-1) < cls l`). Then `X ↦ ∏_l G_l(n̄(X))^{γ_l}` is integrable on the coordinates
`Coord sz → ℝ` of the opposite unipotent radical (Lebesgue measure), where
`G_l = GramFormula.gram l` is the Gram determinant of the rows `l, …, N-1`. (`G_0(n̄(X)) = 1`, so
`γ_0` plays no role.) -/
def RealLeviChartIntegrableStatement : Prop :=
  ∀ (c : ℕ) (sz : Fin c → ℕ) (γ : Fin (∑ i, sz i) → ℝ),
    (∀ l : Fin (∑ i, sz i), 0 < (l : ℕ) → γ l ≤ -(1 / 2)) →
    (∀ k l : Fin (∑ i, sz i), (k : ℕ) + 1 = l →
      RealLeviChart.cls sz k < RealLeviChart.cls sz l → γ l < -(1 / 2)) →
      Integrable fun X : RealLeviChart.Coord sz → ℝ =>
        ∏ l : Fin (∑ i, sz i), GramFormula.gram (l : ℕ) (RealLeviChart.lower sz X) ^ γ l

end Langlands.Archimedean
