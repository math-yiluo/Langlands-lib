import Langlands.Global.AdelicFunctoriality.IdeleClassNorm
import Langlands.Global.NormOneIdeleClassCompact
import Langlands.Global.PositiveRealIdeles

/-! # The normalized absolute value of the actual idele norm -/

noncomputable section

universe u v

namespace Langlands.Global

open NumberField
open scoped NNReal

namespace IdeleAbsoluteValue

variable (F : Type u) [Field F] [NumberField F]

/-- Every continuous positive character trivial on principal ideles kills norm-one ideles. -/
theorem apply_eq_one_of_full_eq_one (χ : Ideles F →ₜ* ℝ≥0ˣ)
    (hχ : ∀ a : Fˣ, χ (diagonalUnits F a) = 1)
    (x : Ideles F) (hx : full F x = 1) : χ x = 1 := by
  obtain ⟨C, hC, _, hcover⟩ := NormOneIdeleClass.exists_isCompact_fundamentalSet F
  have hcont : Continuous (fun y : Ideles F => ((χ y : ℝ≥0) : ℝ)) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp χ.continuous)
  obtain ⟨M, hM⟩ := (hC.image hcont).bddAbove
  have hle (y : Ideles F) (hy : full F y = 1) : ((χ y : ℝ≥0) : ℝ) ≤ 1 := by
    by_contra! hgt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hgt
    have hyn : y ^ n ∈ NormOneIdeleClass.normOneIdeles F := by
      change full F (y ^ n) = 1
      rw [map_pow, hy, one_pow]
    obtain ⟨a, ha⟩ := hcover (y ^ n) hyn
    have hbound := hM (Set.mem_image_of_mem _ ha)
    have heq : ((χ (diagonalUnits F a * y ^ n) : ℝ≥0) : ℝ) =
        ((χ y : ℝ≥0) : ℝ) ^ n := by
      rw [map_mul, hχ, one_mul, map_pow]
      rfl
    rw [heq] at hbound
    exact (not_lt_of_ge hbound) hn
  apply Units.ext
  apply NNReal.eq
  apply le_antisymm (hle x hx)
  have hi := hle x⁻¹ (by rw [map_inv, hx, inv_one])
  have hp : 0 < ((χ x : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (χ x).ne_zero)
  rw [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv] at hi
  exact (inv_le_one₀ hp).mp hi

/-- A principal-trivial continuous positive character is determined by positive scalar ideles. -/
theorem eq_of_positiveRealIdeles (χ : Ideles F →ₜ* ℝ≥0ˣ)
    (hχ : ∀ a : Fˣ, χ (diagonalUnits F a) = 1)
    (hpos : ∀ a : ℝ≥0ˣ, χ (PositiveRealIdeles.full F a) =
      full F (PositiveRealIdeles.full F a)) :
    χ = full F := by
  apply ContinuousMonoidHom.ext
  intro x
  let n := Module.finrank ℚ F
  let s := PositiveRealIdeles.full F (full F x)
  have hs : χ s = full F s := hpos _
  have hy : full F (x ^ n * s⁻¹) = 1 := by
    rw [map_mul, map_pow, map_inv, PositiveRealIdeles.absoluteValue_full]
    exact mul_inv_cancel _
  have hkill := apply_eq_one_of_full_eq_one F χ hχ _ hy
  rw [map_mul, map_pow, map_inv, hs, PositiveRealIdeles.absoluteValue_full] at hkill
  have heq : χ x ^ n = full F x ^ n := (mul_inv_eq_one.mp hkill)
  apply Units.ext
  apply NNReal.eq
  have hn : n ≠ 0 := (Module.finrank_pos (R := ℚ) (M := F)).ne'
  have hr : ((χ x : ℝ≥0) : ℝ) ^ n = ((full F x : ℝ≥0) : ℝ) ^ n :=
    congrArg (fun z : ℝ≥0ˣ => ((z : ℝ≥0) : ℝ)) heq
  exact (pow_left_inj₀ (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) hn).mp hr

end IdeleAbsoluteValue

namespace AdelicFunctoriality

variable (K : Type u) (L : Type v) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L]

omit [NumberField L] in
/-- The positive scalar embedding agrees with the principal map on rational scalars. -/
theorem infiniteRealEmbedding_ratCast (q : ℚ) :
    PositiveRealIdeles.infiniteRealEmbedding L (q : ℝ) =
      algebraMap L (InfiniteAdeles L) (q : L) := by
  funext p
  change PositiveRealIdeles.realEmbedding L p (q : ℝ) =
    algebraMap L p.Completion (q : L)
  simp only [map_ratCast]

/-- Rational density identifies the norm on the real scalar subalgebra at infinity. -/
theorem infiniteAdeleNorm_infiniteRealEmbedding (t : ℝ) :
    infiniteAdeleNorm (K := K) (L := L) (PositiveRealIdeles.infiniteRealEmbedding L t) =
      PositiveRealIdeles.infiniteRealEmbedding K (t ^ Module.finrank K L) := by
  have h := Rat.denseRange_cast.equalizer
    (continuous_infiniteAdeleNorm.comp (PositiveRealIdeles.continuous_infiniteRealEmbedding L))
    ((PositiveRealIdeles.continuous_infiniteRealEmbedding K).comp
      (continuous_id.pow (Module.finrank K L))) (by
        funext q
        change infiniteAdeleNorm (K := K) (L := L)
          (PositiveRealIdeles.infiniteRealEmbedding L (q : ℝ)) = _
        rw [infiniteRealEmbedding_ratCast]
        change (adeleNorm (K := K)
          (algebraMap L (Adeles L) (q : L))).1 = _
        rw [adeleNorm_principal]
        have hn : Algebra.norm K (q : L) = (q : K) ^ Module.finrank K L := by
          rw [← map_ratCast (algebraMap K L), Algebra.norm_algebraMap]
        rw [hn]
        change algebraMap K (InfiniteAdeles K) ((q : K) ^ Module.finrank K L) =
          PositiveRealIdeles.infiniteRealEmbedding K ((q : ℝ) ^ Module.finrank K L)
        simpa only [Rat.cast_pow] using
          (infiniteRealEmbedding_ratCast K (q ^ Module.finrank K L)).symm)
  exact congrFun h t

/-- The actual idele norm sends a positive scalar to its extension-degree power. -/
theorem ideleNorm_positiveRealIdeles (a : ℝ≥0ˣ) :
    ideleNorm (K := K) (L := L) (PositiveRealIdeles.full L a) =
      PositiveRealIdeles.full K (a ^ Module.finrank K L) := by
  apply Units.ext
  apply Prod.ext
  · change infiniteAdeleNorm (PositiveRealIdeles.infiniteRealEmbedding L
      ((a : ℝ≥0) : ℝ)) = _
    rw [infiniteAdeleNorm_infiniteRealEmbedding]
    rfl
  · change finiteAdeleNorm (K := K) (L := L) 1 = 1
    exact map_one _

/-- Pull the genuine normalized absolute value back along the actual full idele norm. -/
def normAbsoluteValueCharacter : Ideles L →ₜ* ℝ≥0ˣ :=
  (IdeleAbsoluteValue.full K).comp (ideleNorm (K := K) (L := L))

/-- The normalized absolute value commutes with the actual full idele norm. -/
theorem full_ideleNorm (x : Ideles L) :
    IdeleAbsoluteValue.full K (ideleNorm (K := K) (L := L) x) =
      IdeleAbsoluteValue.full L x := by
  have heq : normAbsoluteValueCharacter K L = IdeleAbsoluteValue.full L := by
    apply IdeleAbsoluteValue.eq_of_positiveRealIdeles
    · intro a
      change IdeleAbsoluteValue.full K (ideleNorm (K := K) (diagonalUnits L a)) = 1
      rw [show diagonalUnits L a = IdeleGroup.unitEmbedding (𝓞 L) L a from rfl,
        ideleNorm_principal]
      exact IdeleAbsoluteValue.full_diagonalUnits K _
    · intro a
      change IdeleAbsoluteValue.full K
        (ideleNorm (K := K) (L := L) (PositiveRealIdeles.full L a)) = _
      rw [ideleNorm_positiveRealIdeles, PositiveRealIdeles.absoluteValue_full,
        PositiveRealIdeles.absoluteValue_full, ← pow_mul]
      rw [mul_comm, Module.finrank_mul_finrank ℚ K L]
  exact DFunLike.congr_fun heq x

end AdelicFunctoriality
end Langlands.Global
