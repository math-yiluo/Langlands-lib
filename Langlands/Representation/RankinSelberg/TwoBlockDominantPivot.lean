import Langlands.Representation.RankinSelberg.TwoBlockDominantCovarianceData
import Langlands.Representation.RankinSelberg.UnequalRankIwasawaSupportProof

/-! # The separating singleton in the actual dominant matrix -/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockDominantRectangular

open GeneralLinear

universe uF

section Algebra

variable {K : Type uF} [Field K] {n : ℕ}

/-- A row and a column meet in an isolated unit entry. -/
def IsUnitPivot (A : GeneralLinear n K) (i c : Fin n) : Prop :=
  (∀ l, A i l = if c = l then 1 else 0) ∧
    (∀ l, A l c = if i = l then 1 else 0)

theorem IsUnitPivot.mul {A B : GeneralLinear n K} {i c d : Fin n}
    (hA : IsUnitPivot A i c) (hB : IsUnitPivot B c d) :
    IsUnitPivot (A * B) i d := by
  classical
  constructor
  · intro l
    change (A.val * B.val) i l = _
    simp only [Matrix.mul_apply, hA.1]
    simpa using hB.1 l
  · intro l
    change (A.val * B.val) l d = _
    simp only [Matrix.mul_apply, hB.2]
    simpa using hA.2 l

theorem isUnitPivot_permutation (σ : Equiv.Perm (Fin n)) (c : Fin n) :
    IsUnitPivot (permutation n K σ) (σ c) c := by
  constructor
  · intro l
    simp only [permutation_entry, Equiv.apply_eq_iff_eq, eq_comm]
  · intro l
    rw [permutation_entry]

variable {t r j k : ℕ} {m : Fin 2 → ℕ}
variable (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1))

/-- The singleton in the source order `(a,k,1,j,b)`. -/
def singletonIndex : Fin (r + 1) :=
  coordinates h hr (.inr (.inl (.inr (.inl 0))))

/-- Its row after the long Weyl reversal, in order `(b,j,1,k,a)`. -/
def pivotRow : Fin (r + 1) :=
  ⟨m 1 + 1 + j, by have := TwoBlockJacquet.blockRanks_add h; omega⟩

/-- Its column after the block Weyl. This is beyond the appended group block. -/
def pivotColumn : Fin (r + 1) :=
  ⟨t + 1 + j, by clear h m; omega⟩

@[simp] theorem singletonIndex_rev :
    (singletonIndex h hr).rev = pivotRow h hr := by
  apply Fin.ext
  simp only [singletonIndex, coordinates_val, position, Fin.val_rev,
    Fin.val_zero, pivotRow]
  have := TwoBlockJacquet.blockRanks_add h
  omega

@[simp] theorem splitReflection_singletonIndex :
    splitReflection (m 0 + 1) ((j + k + 1) + (m 1 + 1)) (r + 1) (totalRank h hr)
      (singletonIndex h hr) = pivotColumn hr := by
  rw [singletonIndex, splitReflection_coordinates]
  apply Fin.ext
  simp [reflectedIndex, middleCoordinates, pivotColumn, Fin.val_rev]

/-- The two source rectangles both avoid the singleton's row and column. -/
theorem isUnitPivot_rectangleUnipotent
    (x : Matrix (Fin (m 0 + 1)) (Fin k) K)
    (y : Matrix (Fin j) (Fin (m 1 + 1)) K) :
    IsUnitPivot (rectangleUnipotent h hr x y) (singletonIndex h hr) (singletonIndex h hr) := by
  constructor
  · intro l
    obtain ⟨l, rfl⟩ := (coordinates h hr).surjective l
    rw [singletonIndex, rectangleUnipotent_five_entry]
    simp only [Equiv.apply_eq_iff_eq]
    rcases l with l | ((l | (l | l)) | l) <;> simp [rectangleEntries]
  · intro l
    obtain ⟨l, rfl⟩ := (coordinates h hr).surjective l
    rw [singletonIndex, rectangleUnipotent_five_entry]
    simp only [Equiv.apply_eq_iff_eq]
    rcases l with l | ((l | (l | l)) | l) <;> simp [rectangleEntries, eq_comm]

/-- The appended group coordinate does not move the separating column. -/
theorem isUnitPivot_append (g : GeneralLinear (t + 1) K) :
    IsUnitPivot (append hr g) (pivotColumn hr) (pivotColumn hr) := by
  classical
  have hn : ¬(pivotColumn hr).val < t + 1 := by
    dsimp [pivotColumn]
    omega
  constructor
  · intro l
    rw [append_entry]
    simp only [hn, ↓reduceDIte]
  · intro l
    rw [append_entry]
    by_cases hl : l.val < t + 1
    · have hne : pivotColumn hr ≠ l := by
        intro he
        subst l
        exact hn hl
      simp [hl, hn, hne]
    · simp [hl, eq_comm]

/-- The actual JPSS matrix has an isolated unit at row `b+j`, column `t+1+j`,
for every representative and both actual rectangles. -/
theorem isUnitPivot_matrix (g : GeneralLinear (t + 1) K)
    (x : Matrix (Fin (m 0 + 1)) (Fin k) K)
    (y : Matrix (Fin j) (Fin (m 1 + 1)) K) :
    IsUnitPivot (matrix h hr g x y) (pivotRow h hr) (pivotColumn hr) := by
  let σ := splitReflection (m 0 + 1) ((j + k + 1) + (m 1 + 1))
    (r + 1) (totalRank h hr)
  have hW : IsUnitPivot (weylLong (r + 1) K) (pivotRow h hr) (singletonIndex h hr) := by
    have hW := isUnitPivot_permutation (K := K) Fin.revPerm (singletonIndex h hr)
    change IsUnitPivot (weylLong (r + 1) K)
      (singletonIndex h hr).rev (singletonIndex h hr) at hW
    simpa only [singletonIndex_rev] using hW
  have hD : IsUnitPivot (blockWeyl (K := K) h hr)
      (singletonIndex h hr) (pivotColumn hr) := by
    have hσ : σ (pivotColumn hr) = singletonIndex h hr := by
      rw [← splitReflection_singletonIndex h hr]
      change σ (σ (singletonIndex h hr)) = _
      have hinv : σ⁻¹ = σ := splitReflection_inv _ _ _ _
      simpa only [← Equiv.Perm.coe_inv, hinv] using
        σ.symm_apply_apply (singletonIndex h hr)
    simpa only [blockWeyl_permutation, hσ] using
      isUnitPivot_permutation (K := K) σ (pivotColumn hr)
  exact ((hW.mul (isUnitPivot_rectangleUnipotent h hr x y)).mul hD).mul
    (isUnitPivot_append hr g)

end Algebra

section Iwasawa

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- An isolated unit entry fixes the absolute value of the corresponding
Iwasawa diagonal coordinate, even when it is not the last coordinate. -/
theorem normalizedAbs_diagonal_pivot :
    letI := T.valuativeRel
    ∀ {r : ℕ} (M u : GeneralLinear (r + 1) F.Carrier)
      (a : Fin (r + 1) → F.Carrierˣ) (κ : GeneralLinear (r + 1) F.Carrier)
      (i c : Fin (r + 1)),
      IsUnitPivot M i c →
      u ∈ upperUnipotent (r + 1) F.Carrier →
      κ ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer r →
      M = u * Iwasawa.diagonalUnits a * κ →
      T.normalizedAbs (a i : F.Carrier) = 1 := by
  let := T.valuativeRel
  classical
  intro r M u a κ i c hp hu hκ he
  have hκ' := (Conductor.mem_integralSubgroup _ _ κ).mp hκ
  have he' : M * κ⁻¹ = u * Iwasawa.diagonalUnits a := by
    rw [he, mul_assoc, mul_inv_cancel, mul_one]
  have ha : (a i : F.Carrier) = κ⁻¹ c i := by
    have h := congrArg (fun g : GeneralLinear (r + 1) F.Carrier => g i i) he'
    change (M.val * (κ⁻¹).val) i i = (u.val * (Iwasawa.diagonalUnits a).val) i i at h
    rw [Matrix.mul_apply, Iwasawa.diagonalUnits_val, Matrix.mul_diagonal, hu.2 i] at h
    simpa [hp.1] using h.symm
  have heκ : κ = Iwasawa.diagonalUnits a⁻¹ * u⁻¹ * M := by
    rw [map_inv, he]
    group
  have hai : ((a i)⁻¹ : F.Carrier) = κ i c := by
    have h := congrArg (fun g : GeneralLinear (r + 1) F.Carrier => g i c) heκ
    change κ i c =
      (((Iwasawa.diagonalUnits a⁻¹).val * (u⁻¹).val) * M.val) i c at h
    rw [Matrix.mul_apply, Iwasawa.diagonalUnits_val] at h
    simp only [Matrix.diagonal_mul, hp.2, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Pi.inv_apply] at h
    rw [(upperUnipotent (r + 1) F.Carrier).inv_mem hu |>.2 i, mul_one] at h
    simpa only [Units.val_inv_eq_inv_val] using h.symm
  have hle : T.normalizedAbs (a i : F.Carrier) ≤ 1 := by
    rw [ha]
    exact (T.normalizedAbs_le_one_iff_mem_integers _).mpr (hκ'.2 _ _)
  have hile : T.normalizedAbs ((a i)⁻¹ : F.Carrier) ≤ 1 := by
    rw [hai]
    exact (T.normalizedAbs_le_one_iff_mem_integers _).mpr (hκ'.1 _ _)
  have hprod : T.normalizedAbs (a i : F.Carrier) *
      T.normalizedAbs ((a i)⁻¹ : F.Carrier) = 1 := by
    rw [← T.normalizedAbs_mul]
    simp only [mul_inv_cancel₀ (Units.ne_zero _), T.normalizedAbs_one]
  apply le_antisymm hle
  calc
    1 = T.normalizedAbs (a i : F.Carrier) *
        T.normalizedAbs ((a i)⁻¹ : F.Carrier) := hprod.symm
    _ ≤ T.normalizedAbs (a i : F.Carrier) * 1 :=
      mul_le_mul_of_nonneg_left hile (T.normalizedAbs_nonneg _)
    _ = _ := mul_one _

end Iwasawa

end Langlands.RankinSelberg.TwoBlockDominantRectangular
