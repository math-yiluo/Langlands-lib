import Langlands.Representation.Derivative.MirabolicDeterminant
import Langlands.Representation.Mirabolic.MixedProducts
import Langlands.Representation.Derivative.MirabolicMinus

/-! Actual scalar normalization on the lower left mixed subgroup. -/

noncomputable section

open scoped NNReal

namespace Langlands.Derivative.MirabolicProductMinus

open GeneralLinear GeneralLinear.Mirabolic GeneralLinear.Mirabolic.MixedProduct

section Determinants

universe u

variable {R : Type u} [CommRing R] {k r n : ℕ}

/-- The entire determinant of a lower left mixed-subgroup element is the product
of the determinants of its actual two coefficient blocks. -/
theorem leftPhiSubgroup_determinant (h : leftSubgroup k r R) :
    GeneralLinear.determinant h.val.val =
      GeneralLinear.determinant (leftProjection h).1 *
        GeneralLinear.determinant (leftProjection h).2.val := by
  apply Units.ext
  change Matrix.det h.val.val.val =
    Matrix.det (TwoBlock.A (leftBlocks h)) * Matrix.det (TwoBlock.D (leftBlocks h))
  calc
    _ = Matrix.det (leftBlocks h).val.val :=
      (Matrix.det_reindex_self (leftIndex k r).symm h.val.val.val).symm
    _ = _ := by
      rw [TwoBlock.display, Matrix.det_fromBlocks_zero₂₁]

end Determinants

section Normalization

universe uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

private theorem determinantNorm_successor_for_leftPhi {n : ℕ}
    (g : mirabolic n F.Carrier) :
    T.determinantNorm (n + 2) (successor g).val =
      T.determinantNorm (n + 1) g.val :=
  congrArg T.normalizedAbsUnits (JacquetNormalization.determinant_successor g)

/-- The supplied normalized determinant norm factors through the actual blocks. -/
theorem leftPhiSubgroup_determinantNorm {k r : ℕ}
    (h : leftSubgroup k r F.Carrier) :
    T.determinantNorm (k + r + 1) h.val.val =
      T.determinantNorm k (leftProjection h).1 *
        T.determinantNorm (r + 1) (leftProjection h).2.val := by
  change T.normalizedAbsUnits _ = T.normalizedAbsUnits _ * T.normalizedAbsUnits _
  rw [leftPhiSubgroup_determinant, map_mul]

/-- Ambient inverse-half normalization times the higher left coefficient
character, restricted to the actual successor coefficient pair. -/
def leftPhiSectionCharacter (k r : ℕ) : leftSubgroup k r F.Carrier →* ℂˣ :=
  (Mirabolic.phiMinusCharacter T (k + r)).comp (leftSubgroup k r F.Carrier).subtype *
    (T.leftLeviCharacter k (r + 1)).comp
      (((MonoidHom.id (GeneralLinear k F.Carrier)).prodMap
        (successor (n := r))).comp leftProjection)

@[simp] theorem leftPhiSectionCharacter_apply {k r : ℕ}
    (h : leftSubgroup k r F.Carrier) :
    leftPhiSectionCharacter T k r h =
      Mirabolic.phiMinusCharacter T (k + r) h.val *
        T.leftLeviCharacter k (r + 1) ((leftProjection h).1, successor (leftProjection h).2) :=
  rfl

private theorem leftPhi_scalar_normalization (x y : ℝ≥0ˣ) (k r : ℕ) :
    (((((x * y : ℝ≥0ˣ) : ℝ≥0) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ((((x : ℝ≥0) : ℝ) ^ (((r + 1 + 1 : ℕ) : ℝ) / 2) : ℝ) : ℂ) *
          ((((y : ℝ≥0) : ℝ) ^ (-((k : ℝ) / 2)) : ℝ) : ℂ) =
      ((((x : ℝ≥0) : ℝ) ^ (((r + 1 : ℕ) : ℝ) / 2) : ℝ) : ℂ) *
        ((((y : ℝ≥0) : ℝ) ^ (-((k : ℝ) / 2)) : ℝ) : ℂ) *
          ((((y : ℝ≥0) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  have hx : (0 : ℝ) < ((x : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt x)
  have hy : (0 : ℝ) < ((y : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt y)
  have ha : ((x : ℝ≥0) : ℝ) ^ (-(1 / 2 : ℝ)) *
      ((x : ℝ≥0) : ℝ) ^ (((r + 1 + 1 : ℕ) : ℝ) / 2) =
        ((x : ℝ≥0) : ℝ) ^ (((r + 1 : ℕ) : ℝ) / 2) := by
    rw [← Real.rpow_add hx]
    congr 1
    push_cast
    ring
  simp only [Units.val_mul, NNReal.coe_mul, Real.mul_rpow hx.le hy.le,
    Complex.ofReal_mul]
  calc
    _ = ((((x : ℝ≥0) : ℝ) ^ (-(1 / 2 : ℝ)) *
        ((x : ℝ≥0) : ℝ) ^ (((r + 1 + 1 : ℕ) : ℝ) / 2) : ℝ) : ℂ) *
        ((((y : ℝ≥0) : ℝ) ^ (-((k : ℝ) / 2)) : ℝ) : ℂ) *
        ((((y : ℝ≥0) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
          push_cast
          ring
    _ = _ := by rw [ha]

/-- The entire higher coefficient character becomes the lower left character
and the source Phi inverse-half character, with no residual scalar. -/
theorem leftPhiSectionCharacter_eq (k r : ℕ) :
    leftPhiSectionCharacter T k r =
      (T.leftLeviCharacter k r).comp leftProjection *
        (Mirabolic.phiMinusCharacter T r).comp
          ((MonoidHom.snd _ _).comp leftProjection) := by
  apply MonoidHom.ext
  intro h
  apply Units.ext
  rw [leftPhiSectionCharacter_apply]
  simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul,
    T.leftLeviCharacter_apply, Mirabolic.phiMinusCharacter, coe_realPowerCharacter,
    MonoidHom.coe_snd, Subgroup.coe_subtype,
    determinantNorm_successor_for_leftPhi T, leftPhiSubgroup_determinantNorm T]
  simpa only [Units.val_mul, mul_assoc] using leftPhi_scalar_normalization
    (T.determinantNorm k (leftProjection h).1)
    (T.determinantNorm (r + 1) (leftProjection h).2.val) k r

end Normalization

end Langlands.Derivative.MirabolicProductMinus
