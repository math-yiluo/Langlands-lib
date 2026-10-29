import Langlands.Representation.RankinSelberg.RankOneExtensionSpanTransfer
import Langlands.Representation.RankinSelberg.RankOneExtensionLowerCovariance
import Langlands.Group.GL.LowerBlockQuotientCoordinates

/-!
# Whittaker characters on the rank-one extension cells

For a Whittaker function `W` of rank `(1 + (t + 1)) + k`, read through the standard rank
inclusion `ι = diag(·, I_(k+1))`:
`W(ι(u(y) z)) = ψ(y_t) W(ι z)` and `W(ι(B(n, 0, 1) z)) = θ(n) W(ι z)` for `n ∈ N_(t+1)`.
The scalar coefficient of a lower induced section transforms by the inverse character:
`c_f(B(n, 0, 1) z) = θ(n)⁻¹ c_f(z)`.
-/

noncomputable section

namespace Langlands.RankinSelberg

open GeneralLinear Matrix HarmonicAnalysis Whittaker
open scoped NNReal

universe uF uW

section Entries

variable {K : Type uF} [Field K] {t : ℕ}

/-- Numeric entries of the upper cell `u(y) = [I, y; 0, 1]` in `GL(1 + (t + 1))`. -/
theorem rankOneExtensionUpperCell_entry (y : Fin (t + 1) → K) (i j : Fin (1 + (t + 1))) :
    rankOneExtensionUpperCell t y i j =
      if hi : i.val < t + 1 then
        if j.val < t + 1 then (if i.val = j.val then 1 else 0) else y ⟨i.val, hi⟩
      else if j.val < t + 1 then 0 else 1 := by
  obtain ⟨i, rfl⟩ := (rankOneExtensionCellCoordinates t).surjective i
  obtain ⟨j, rfl⟩ := (rankOneExtensionCellCoordinates t).surjective j
  rw [rankOneExtensionUpperCell_apply]
  rcases i with i | i <;> rcases j with j | j
  · simp [rankOneExtensionCellCoordinates, Fin.is_le, Matrix.one_apply, Fin.ext_iff]
  · simp [rankOneExtensionCellCoordinates, Fin.val_eq_zero, not_lt.2 (Fin.is_le i)]
  · simp [rankOneExtensionCellCoordinates, Fin.val_eq_zero, not_lt.2 (Fin.is_le j)]
  · obtain rfl := Subsingleton.elim i j
    simp [rankOneExtensionCellCoordinates, Fin.val_eq_zero]

/-- The first-superdiagonal sum of `ι u(y)` is the last coordinate `y_t`. -/
theorem superdiagonal_rankInclusion_upperCell (k : ℕ) (y : Fin (t + 1) → K) :
    ∑ i : Fin ((1 + (t + 1)) + k),
        (rankInclusion (k + 1) (rankOneExtensionUpperCell t y) :
          Matrix (Fin ((1 + (t + 1)) + k + 1)) (Fin ((1 + (t + 1)) + k + 1)) K)
          i.castSucc i.succ = y (Fin.last t) := by
  rw [Finset.sum_eq_single (⟨t, by omega⟩ : Fin ((1 + (t + 1)) + k))]
  · rw [rankInclusion_entry]
    simp only [Fin.val_castSucc, Fin.val_succ, Fin.ext_iff, rankOneExtensionUpperCell_entry]
    split_ifs <;> first | rfl | omega
  · intro i _ hi
    have hi' : i.val ≠ t := fun h => hi (Fin.ext h)
    rw [rankInclusion_entry]
    simp only [Fin.val_castSucc, Fin.val_succ, Fin.ext_iff, rankOneExtensionUpperCell_entry]
    split_ifs <;> first | rfl | omega
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The first-superdiagonal sum of `ι B(n, 0, 1)` is that of `n`. -/
theorem superdiagonal_rankInclusion_lowerBlock (k : ℕ) (n : Langlands.GeneralLinear (t + 1) K) :
    ∑ i : Fin ((1 + (t + 1)) + k),
        (rankInclusion (k + 1) (rankOneExtensionLowerBlock t n 0 1) :
          Matrix (Fin ((1 + (t + 1)) + k + 1)) (Fin ((1 + (t + 1)) + k + 1)) K)
          i.castSucc i.succ =
      ∑ i : Fin t, (n : Matrix (Fin (t + 1)) (Fin (t + 1)) K) i.castSucc i.succ := by
  let f : ℕ → K := fun i =>
    if h : i + 1 < t + 1 then (n : Matrix (Fin (t + 1)) (Fin (t + 1)) K) ⟨i, by omega⟩ ⟨i + 1, h⟩
    else 0
  have hL : ∀ i : Fin ((1 + (t + 1)) + k),
      (rankInclusion (k + 1) (rankOneExtensionLowerBlock t n 0 1) :
        Matrix (Fin ((1 + (t + 1)) + k + 1)) (Fin ((1 + (t + 1)) + k + 1)) K)
        i.castSucc i.succ = f i.val := by
    intro i
    rw [rankInclusion_entry]
    simp only [Fin.val_castSucc, Fin.val_succ, Fin.ext_iff, rankOneExtensionLowerBlock_entry, f]
    split_ifs <;> first | rfl | omega
  have hR : ∀ i : Fin t,
      (n : Matrix (Fin (t + 1)) (Fin (t + 1)) K) i.castSucc i.succ = f i.val := by
    intro i
    have := i.isLt
    simp only [f]
    split_ifs
    · rfl
    · omega
  simp only [hL, hR]
  rw [Fin.sum_univ_eq_sum_range f, Fin.sum_univ_eq_sum_range f]
  symm
  apply Finset.sum_subset
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro i _ hi
    simp only [Finset.mem_range, not_lt] at hi
    simp only [f]
    split_ifs
    · omega
    · rfl

end Entries

section Whittaker

variable {K : Type uF} [Field K] [TopologicalSpace K] (ψ : UnitaryAdditiveCharacter K) {t : ℕ}

/-- `W(ι(u(y) z)) = ψ(y_t) W(ι z)`. -/
theorem whittaker_rankInclusion_upperCell_mul {k : ℕ}
    (W : WhittakerFunctions ψ ((1 + (t + 1)) + k)) (y : Fin (t + 1) → K)
    (z : Langlands.GeneralLinear (1 + (t + 1)) K) :
    W.val (rankInclusion (k + 1) (rankOneExtensionUpperCell t y * z)) =
      ψ.complex (y (Fin.last t)) * W.val (rankInclusion (k + 1) z) := by
  have hmem : rankInclusion (k + 1) (rankOneExtensionUpperCell t y) ∈
      upperUnipotent ((1 + (t + 1)) + k + 1) K :=
    rankInclusion_mem_upperUnipotent (rankOneExtensionUpperCell_mem_upperUnipotent y)
  rw [map_mul]
  have h := W.property ⟨_, hmem⟩ (rankInclusion (k + 1) z)
  refine h.trans ?_
  rw [standardCharacter_apply]
  congr 2
  exact superdiagonal_rankInclusion_upperCell k y

/-- `W(ι(B(n, 0, 1) z)) = θ(n) W(ι z)` for `n ∈ N_(t+1)`. -/
theorem whittaker_rankInclusion_lowerBlock_mul {k : ℕ}
    (W : WhittakerFunctions ψ ((1 + (t + 1)) + k)) (n : upperUnipotent (t + 1) K)
    (z : Langlands.GeneralLinear (1 + (t + 1)) K) :
    W.val (rankInclusion (k + 1) (rankOneExtensionLowerBlock t n.val 0 1 * z)) =
      (standardCharacter ψ t n : ℂ) * W.val (rankInclusion (k + 1) z) := by
  have hmem : rankInclusion (k + 1) (rankOneExtensionLowerBlock t n.val 0 1) ∈
      upperUnipotent ((1 + (t + 1)) + k + 1) K :=
    rankInclusion_mem_upperUnipotent (rankOneExtensionLowerBlock_mem_upperUnipotent n.val n.2)
  rw [map_mul]
  have h := W.property ⟨_, hmem⟩ (rankInclusion (k + 1) z)
  refine h.trans ?_
  rw [standardCharacter_apply, standardCharacter_apply]
  congr 2
  exact superdiagonal_rankInclusion_lowerBlock k n.val

end Whittaker

section Coefficient

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

theorem rankOneExtensionTensorContraction_smul (c : ℂ) (ℓ : W →ₗ[ℂ] ℂ) :
    rankOneExtensionTensorContraction (c • ℓ) = c • rankOneExtensionTensorContraction ℓ := by
  apply LinearMap.ext
  intro T
  simp only [rankOneExtensionTensorContraction, Shahidi.pairFunctional_smul_right]
  rfl

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (t : ℕ)
  (χ : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier)
  (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)

/-- `c_f(B(n, 0, 1) z) = θ(n)⁻¹ c_f(z)` for `n ∈ N_(t+1)`. -/
theorem rankOneExtensionLowerSectionCoefficient_unipotent_mul
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ℓ : letI := F.canonicalTopologicalData.topology; Whittaker.glInverseFunctionals ψ t σ)
    (f : rankOneExtensionLowerSection F t χ σ) (n : upperUnipotent (t + 1) F.Carrier)
    (z : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    rankOneExtensionLowerSectionCoefficient F t χ σ ψ ℓ f
        (rankOneExtensionLowerBlock t n.val 0 1 * z) =
      ((inverseStandardCharacter ψ t n : ℂˣ) : ℂ) *
        rankOneExtensionLowerSectionCoefficient F t χ σ ψ ℓ f z := by
  let := F.canonicalTopologicalData.topology
  rw [rankOneExtensionLowerSectionCoefficient_lowerBlock_mul]
  have hdet : F.canonicalTopologicalData.determinantNorm (t + 1) n.val = 1 := by
    apply Units.ext
    rw [PadicField.TopologicalData.determinantNorm, MonoidHom.comp_apply]
    have : GeneralLinear.determinant n.val = 1 := Units.ext (unipotent_det n)
    rw [this, map_one]
  have hℓ : ℓ.val ∘ₗ σ n.val = ((inverseStandardCharacter ψ t n : ℂˣ) : ℂ) • ℓ.val := by
    apply LinearMap.ext
    intro w
    exact ℓ.property n w
  rw [hdet, map_one, one_pow, div_one, Units.val_one, NNReal.sqrt_one, NNReal.coe_one,
    Complex.ofReal_one, inv_one, one_mul, map_one, Units.val_one, one_mul, hℓ,
    rankOneExtensionTensorContraction_smul, LinearMap.smul_apply, smul_eq_mul]
  rfl

end Coefficient

end Langlands.RankinSelberg
