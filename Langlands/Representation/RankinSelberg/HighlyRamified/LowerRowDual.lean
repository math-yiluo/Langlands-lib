import Langlands.Representation.RankinSelberg.HighlyRamified.DualSmear
import Langlands.Representation.RankinSelberg.QuotientIntegrals
import Langlands.Representation.RankinSelberg.FunctionalEquationStatement

/-!
# Inverse transposes of the lower-row matrices

`ᵗū_x⁻¹` is upper unipotent with last column `(-ᵗx, 1)`; its first-superdiagonal sum is
`-x_m`. Conjugating `ū_x` by `diag(C,1)` gives `ū_(x C⁻¹)`. Hence an inverse Whittaker function
`f'` on `GL_(m+2)` satisfies `f'(diag(B,1) ᵗū_x⁻¹) = ψ(Σ_j B_(m,j) x_j) f'(diag(B,1))`.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open Matrix Langlands.GeneralLinear Langlands.Whittaker

universe uF

variable {F : Type uF} [Field F] {m : ℕ}

theorem lowerRow_castSucc_castSucc (x : Matrix (Fin 1) (Fin (m + 1)) F) (i j : Fin (m + 1)) :
    lowerRow x i.castSucc j.castSucc = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j := by
  change lowerBlockPair 1 x 1 (i.castAdd 1) (j.castAdd 1) = _
  rw [lowerBlockPair_11]
  rfl

theorem lowerRow_castSucc_last (x : Matrix (Fin 1) (Fin (m + 1)) F) (i : Fin (m + 1)) :
    lowerRow x i.castSucc (Fin.last (m + 1)) = 0 := by
  change lowerBlockPair 1 x 1 (i.castAdd 1) (Fin.last (m + 1)) = _
  rw [← natAdd_zero_eq_last, lowerBlockPair_12]

theorem lowerRow_last_castSucc (x : Matrix (Fin 1) (Fin (m + 1)) F) (j : Fin (m + 1)) :
    lowerRow x (Fin.last (m + 1)) j.castSucc = x 0 j := by
  change lowerBlockPair 1 x 1 (Fin.last (m + 1)) (j.castAdd 1) = _
  rw [← natAdd_zero_eq_last, lowerBlockPair_21]

theorem lowerRow_last_last (x : Matrix (Fin 1) (Fin (m + 1)) F) :
    lowerRow x (Fin.last (m + 1)) (Fin.last (m + 1)) = 1 := by
  change lowerBlockPair 1 x 1 (Fin.last (m + 1)) (Fin.last (m + 1)) = _
  rw [← natAdd_zero_eq_last, lowerBlockPair_22]
  rfl

theorem lowerRow_inv (x : Matrix (Fin 1) (Fin (m + 1)) F) : (lowerRow x)⁻¹ = lowerRow (-x) := by
  rw [inv_eq_iff_mul_eq_one, ← lowerRow_add, add_neg_cancel, lowerRow_zero]

/-- `ᵗū_x⁻¹` is upper unipotent. -/
theorem inverseTranspose_lowerRow_mem (x : Matrix (Fin 1) (Fin (m + 1)) F) :
    inverseTranspose (m + 1 + 1) F (lowerRow x) ∈ upperUnipotent (m + 1 + 1) F := by
  refine ⟨?_, fun i => ?_⟩
  · intro i j hij
    change inverseTranspose (m + 1 + 1) F (lowerRow x) i j = 0
    rw [inverseTranspose_entry, lowerRow_inv]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · rw [lowerRow_castSucc_castSucc]
        have : j' ≠ i' := by
          intro h; subst h; exact lt_irrefl _ hij
        rw [Matrix.one_apply_ne this]
      · exact absurd hij (not_lt.mpr (Fin.le_last _))
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · exact lowerRow_castSucc_last _ _
      · exact absurd hij (lt_irrefl _)
  · change inverseTranspose (m + 1 + 1) F (lowerRow x) i i = 1
    rw [inverseTranspose_entry, lowerRow_inv]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · rw [lowerRow_castSucc_castSucc, Matrix.one_apply_eq]
    · exact lowerRow_last_last _

/-- The first-superdiagonal sum of `ᵗū_x⁻¹` is `-x_m`. -/
theorem inverseTranspose_lowerRow_superdiagonal (x : Matrix (Fin 1) (Fin (m + 1)) F) :
    ∑ i : Fin (m + 1), inverseTranspose (m + 1 + 1) F (lowerRow x) i.castSucc i.succ =
      -x 0 (Fin.last m) := by
  simp_rw [inverseTranspose_entry, lowerRow_inv]
  rw [Fin.sum_univ_castSucc]
  have hlast : lowerRow (-x) (Fin.last (m + 1)) (Fin.last m).castSucc = -x 0 (Fin.last m) := by
    rw [lowerRow_last_castSucc]
    rfl
  have hrest : ∀ i : Fin m, lowerRow (-x) i.castSucc.succ i.castSucc.castSucc = 0 := by
    intro i
    rw [← Fin.castSucc_succ, lowerRow_castSucc_castSucc]
    have : i.succ ≠ i.castSucc := by
      intro h; have := congrArg Fin.val h; simp at this
    rw [Matrix.one_apply_ne this]
  simp only [hrest, Finset.sum_const_zero, zero_add, Fin.succ_last, hlast]

/-- `diag(C,1) ū_x = ū_(x C⁻¹) diag(C,1)`. -/
theorem rankInclusion_mul_lowerRow (C : GeneralLinear (m + 1) F)
    (x : Matrix (Fin 1) (Fin (m + 1)) F) :
    rankInclusion 1 C * lowerRow x =
      lowerRow (x * (C⁻¹ : GeneralLinear (m + 1) F).val) * rankInclusion 1 C := by
  have h1 : rankInclusion 1 C = (lowerBlockPair C 0 1 : GeneralLinear (m + 1 + 1) F) := by
    rw [lowerBlockPair_eq_rankInclusion_mul, ← lowerRow, lowerRow_zero, mul_one]
  rw [h1, lowerRow, lowerRow, lowerBlockPair_mul_lowerBlockPair,
    lowerBlockPair_mul_lowerBlockPair]
  congr 1
  · simp
  · simp only [zero_add, Units.val_one, Matrix.mul_one, OneMemClass.coe_one,
      Matrix.one_mul, add_zero, Matrix.mul_assoc]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]

/-- `ᵗdiag(B,1)⁻¹ = diag(ᵗB⁻¹, 1)`. -/
theorem inverseTranspose_rankInclusion (B : GeneralLinear (m + 1) F) :
    inverseTranspose (m + 1 + 1) F (rankInclusion 1 B) =
      rankInclusion 1 (inverseTranspose (m + 1) F B) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [inverseTranspose_entry, ← map_inv]
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
  · rw [Iwasawa.rankInclusion_castSucc_castSucc, Iwasawa.rankInclusion_castSucc_castSucc,
      inverseTranspose_entry]
  · rw [Iwasawa.rankInclusion_last_castSucc, Iwasawa.rankInclusion_castSucc_last]
  · rw [Iwasawa.rankInclusion_castSucc_last, Iwasawa.rankInclusion_last_castSucc]
  · rw [Iwasawa.rankInclusion_last_last, Iwasawa.rankInclusion_last_last]

section Whittaker

variable [TopologicalSpace F]

/-- `f'(diag(B,1) ᵗū_x⁻¹) = ψ(Σ_j B_(m,j) x_j) f'(diag(B,1))` for an inverse Whittaker
function `f'` on `GL_(m+2)`. -/
theorem inverseWhittaker_mul_inverseTranspose_lowerRow
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F)
    (f' : RankinSelberg.InverseWhittakerFunctions ψ (m + 1)) (B : GeneralLinear (m + 1) F)
    (x : Matrix (Fin 1) (Fin (m + 1)) F) :
    f'.val (rankInclusion 1 B * inverseTranspose (m + 1 + 1) F (lowerRow x)) =
      ψ.complex (∑ j, B (Fin.last m) j * x 0 j) * f'.val (rankInclusion 1 B) := by
  set C := inverseTranspose (m + 1) F B with hC
  set y : Matrix (Fin 1) (Fin (m + 1)) F := x * (C⁻¹ : GeneralLinear (m + 1) F).val with hy
  have hB : rankInclusion 1 B = inverseTranspose (m + 1 + 1) F (rankInclusion 1 C) := by
    rw [inverseTranspose_rankInclusion, hC, inverseTranspose_involutive]
  have hdec : rankInclusion 1 B * inverseTranspose (m + 1 + 1) F (lowerRow x) =
      inverseTranspose (m + 1 + 1) F (lowerRow y) * rankInclusion 1 B := by
    rw [hB, ← map_mul, rankInclusion_mul_lowerRow, map_mul]
  set u : upperUnipotent (m + 1 + 1) F :=
    ⟨inverseTranspose (m + 1 + 1) F (lowerRow y), inverseTranspose_lowerRow_mem y⟩ with hu
  rw [hdec, show inverseTranspose (m + 1 + 1) F (lowerRow y) = u.val from rfl, f'.property u,
    inverseStandardCharacter_apply]
  congr 1
  rw [show (∑ i : Fin (m + 1), u.val i.castSucc i.succ) = -y 0 (Fin.last m) from
    inverseTranspose_lowerRow_superdiagonal y]
  rw [AddChar.map_neg_eq_inv, inv_inv]
  congr 1
  rw [hy, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hC, ← map_inv, inverseTranspose_entry, inv_inv, mul_comm]

omit [TopologicalSpace F] in
/-- `w ᵗ(w ᵗM⁻¹ ū)⁻¹ = M ᵗū⁻¹`. -/
theorem weylLong_mul_inverseTranspose_dual (M u : GeneralLinear (m + 1 + 1) F) :
    weylLong (m + 1 + 1) F * inverseTranspose (m + 1 + 1) F
        (weylLong (m + 1 + 1) F * inverseTranspose (m + 1 + 1) F M * u) =
      M * inverseTranspose (m + 1 + 1) F u := by
  rw [map_mul, map_mul, inverseTranspose_weylLong, inverseTranspose_involutive, ← mul_assoc,
    ← mul_assoc, weylLong_mul_self, one_mul]

/-- The smeared second dual function at `w ᵗdiag(B,1)⁻¹`: for
`Φ(y) = ∫ S(x) f̃'(y ū_x) dx`, `Φ(w ᵗdiag(B,1)⁻¹) = f'(diag(B,1)) ∫ S(x) ψ(Σ_j B_(m,j) x_j) dx`. -/
theorem smearedSecondDual_at_dual [IsTopologicalRing F]
    [MeasurableSpace (Matrix (Fin 1) (Fin (m + 1)) F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F)
    (f' : RankinSelberg.InverseWhittakerFunctions ψ (m + 1)) (B : GeneralLinear (m + 1) F)
    (μx : MeasureTheory.Measure (Matrix (Fin 1) (Fin (m + 1)) F))
    (S : Matrix (Fin 1) (Fin (m + 1)) F → ℂ) :
    ∫ x, S x * (RankinSelberg.secondDualFunction ψ (m + 1) f').val
        (weylLong (m + 1 + 1) F * inverseTranspose (m + 1 + 1) F (rankInclusion 1 B) *
          lowerRow x) ∂μx =
      f'.val (rankInclusion 1 B) *
        ∫ x, S x * ψ.complex (∑ j, B (Fin.last m) j * x 0 j) ∂μx := by
  rw [← MeasureTheory.integral_const_mul]
  congr 1
  funext x
  rw [RankinSelberg.secondDualFunction_apply, weylLong_mul_inverseTranspose_dual,
    inverseWhittaker_mul_inverseTranspose_lowerRow]
  ring

end Whittaker

end Langlands.RankinSelberg.HighlyRamified
