import Langlands.Representation.Archimedean.RealCartanTransverseDeterminant
import Langlands.Representation.Archimedean.RealCartanBlockLayout
import Mathlib.Order.Interval.Finset.Fin

/-! # Borel normalization of the transverse Cartan determinant -/

noncomputable section

open Matrix Set
open scoped Matrix.Norms.Operator

namespace Langlands.Archimedean.RealCartanRadialWeight

open Langlands.LocalFactor.Archimedean GramFormula PrincipalSeriesExtension
  RealCartanArgumentJacobian RealCartanBlockLayout RealCartanLowerCoordinates
  RealCartanOffBlockDeterminant RealCartanPeakTest RealCartanTransverseDeterminant RealLeviChart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local notation "M" n:max => Matrix (Fin n) (Fin n) ℝ
local notation "K" n:max => Matrix.unitaryGroup (Fin n) ℝ
local notation "G" n:max => Langlands.GeneralLinear n ℝ

section Sums

private def lowerByRow (n : ℕ) : LowerIndex n ≃ Σ p : Fin n, Iio p where
  toFun z := ⟨z.1.1, ⟨z.1.2, z.2⟩⟩
  invFun z := ⟨(z.1, z.2.1), z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def lowerByColumn (n : ℕ) : LowerIndex n ≃ Σ q : Fin n, Ioi q where
  toFun z := ⟨z.1.2, ⟨z.1.1, z.2⟩⟩
  invFun z := ⟨(z.2.1, z.1), z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem sum_lower_pair {n : ℕ} (f : Fin n → ℝ) :
    ∑ p : LowerIndex n, (f p.1.2 - f p.1.1) / 2 =
      ∑ i : Fin n, f i * (((n : ℝ) - 1) / 2 - (i.val : ℝ)) := by
  classical
  have hrow : ∑ p : LowerIndex n, f p.1.1 = ∑ i : Fin n, (i.val : ℝ) * f i := by
    calc
      _ = ∑ z : Σ i : Fin n, Iio i, f z.1 := Fintype.sum_equiv (lowerByRow n) _ _ (fun _ => rfl)
      _ = _ := by simp [Fintype.sum_sigma, Finset.sum_const, Fin.card_Iio]
  have hcol : ∑ p : LowerIndex n, f p.1.2 = ∑ i : Fin n, ((n : ℝ) - 1 - (i.val : ℝ)) * f i := by
    calc
      _ = ∑ z : Σ i : Fin n, Ioi i, f z.1 := Fintype.sum_equiv (lowerByColumn n) _ _ (fun _ => rfl)
      _ = _ := by
        rw [Fintype.sum_sigma]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_Ioi, Fin.card_Ioi]
        rw [Nat.cast_sub (by have := i.isLt; omega), Nat.cast_sub (by have := i.isLt; omega)]
        simp
  simp_rw [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_sub_distrib, hcol, hrow]
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

variable {c : ℕ} (sz : Fin c → ℕ)
local notation "N" => ∑ i, sz i

private def rectCoordEquiv : (Σ b : OffPair c, Fin (sz b.1.1) × Fin (sz b.1.2)) ≃ Coord sz :=
  Equiv.ofBijective (fun z => ⟨(pos sz z.1.1.1 z.2.1, pos sz z.1.1.2 z.2.2),
    by simpa only [cls_pos] using z.1.2⟩) (by
    constructor
    · rintro ⟨b, p, q⟩ ⟨b', p', q'⟩ h
      have h₁ := finSigmaFinEquiv.injective (congrArg (fun z : Coord sz => z.1.1) h)
      have h₂ := finSigmaFinEquiv.injective (congrArg (fun z : Coord sz => z.1.2) h)
      have hbb : b = b' := Subtype.ext (Prod.ext (congrArg Sigma.fst h₁) (congrArg Sigma.fst h₂))
      subst b'
      congr 1
      exact Prod.ext (eq_of_heq (Sigma.mk.inj_iff.mp h₁).2) (eq_of_heq (Sigma.mk.inj_iff.mp h₂).2)
    · intro z
      obtain ⟨p, hp⟩ := pos_cls sz z.1.1
      obtain ⟨q, hq⟩ := pos_cls sz z.1.2
      exact ⟨⟨⟨(cls sz z.1.1, cls sz z.1.2), z.2⟩, (p, q)⟩,
        Subtype.ext (Prod.ext hp hq)⟩)

private theorem sum_lower_by_blocks (f : Fin c → ℝ) :
    ∑ p : LowerIndex N, (f (cls sz p.1.2) - f (cls sz p.1.1)) / 2 =
      ∑ b : OffPair c, ((sz b.1.1 * sz b.1.2 : ℕ) : ℝ) * (f b.1.2 - f b.1.1) / 2 := by
  classical
  rw [← (lowerIndexEquiv sz).sum_comp]
  rw [Fintype.sum_sum_type]
  have hwithin : ∑ p : WithinIndex sz, (f (cls sz (lowerIndexEquiv sz (.inr p)).1.2) -
      f (cls sz (lowerIndexEquiv sz (.inr p)).1.1)) / 2 = 0 := by
    exact Finset.sum_eq_zero fun p _ => by simp [lowerIndexEquiv_inr, cls_eq_of_withinIndex sz p]
  rw [hwithin, add_zero, ← (rectCoordEquiv sz).sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun b _ => ?_
  have he (p : Fin (sz b.1.1) × Fin (sz b.1.2)) :
      (f (cls sz (lowerIndexEquiv sz (.inl (rectCoordEquiv sz ⟨b, p⟩))).1.2) -
        f (cls sz (lowerIndexEquiv sz (.inl (rectCoordEquiv sz ⟨b, p⟩))).1.1)) / 2 =
        (f b.1.2 - f b.1.1) / 2 := by
    simp [lowerIndexEquiv_inl, rectCoordEquiv, cls_pos]
  simp_rw [he, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  ring

end Sums

section Modulus

variable {c : ℕ} (sz : Fin c → ℕ)
local notation "N" => ∑ i, sz i

/-- The positive Borel half-density on the block-scalar diagonal. -/
def borelWeight (d : Fin c → ℝ) : ℝ :=
  ∏ p : Fin N, (d (cls sz p)) ^ (((N : ℝ) - 1) / 2 - (p.val : ℝ))

theorem borelWeight_pos (d : Fin c → ℝ) (hd : ∀ i, 0 < d i) : 0 < borelWeight sz d :=
  Finset.prod_pos fun p _ => Real.rpow_pos_of_pos (hd (cls sz p)) _

private theorem borelWeight_eq_product (d : Fin c → ℝ) (hd : ∀ i, 0 < d i) :
    borelWeight sz d = ∏ b : OffPair c, Real.sqrt ((d b.1.2 / d b.1.1) ^ (sz b.1.1 * sz b.1.2)) := by
  let f (i : Fin c) := Real.log (d i)
  have h₁ := sum_lower_pair (f ∘ cls sz)
  have h₂ := sum_lower_by_blocks sz f
  have hlog (b : OffPair c) : Real.sqrt ((d b.1.2 / d b.1.1) ^ (sz b.1.1 * sz b.1.2)) =
      Real.exp (((sz b.1.1 * sz b.1.2 : ℕ) : ℝ) * (f b.1.2 - f b.1.1) / 2) := by
    have hpos : 0 < d b.1.2 / d b.1.1 := div_pos (hd _) (hd _)
    rw [← Real.exp_log (Real.sqrt_pos.2 (pow_pos hpos _)), Real.log_sqrt (pow_nonneg hpos.le _),
      Real.log_pow, Real.log_div (hd _).ne' (hd _).ne']
  calc
    _ = ∏ p : Fin N, Real.exp (f (cls sz p) * (((N : ℝ) - 1) / 2 - (p.val : ℝ))) :=
      Finset.prod_congr rfl fun p _ => Real.rpow_def_of_pos (hd _) _
    _ = ∏ b : OffPair c, Real.exp (((sz b.1.1 * sz b.1.2 : ℕ) : ℝ) * (f b.1.2 - f b.1.1) / 2) := by
      rw [← Real.exp_sum, ← Real.exp_sum]
      congr 1
      simpa only [Function.comp_apply, Nat.cast_sum] using h₁.symm.trans h₂
    _ = _ := Finset.prod_congr rfl fun b _ => (hlog b).symm

private theorem abs_det_orthogonal_block (B : K N) (hB : BlockZero sz (B : M N)) (i : Fin c) :
    |((B : M N).submatrix (pos sz i) (pos sz i)).det| = 1 := by
  have hunit : (B : M N) * (B : M N)ᵀ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.mem_unitaryGroup_iff.mp B.2
  have h := congrArg Matrix.det (RealLeviTorus.diagBlock_mul_transpose hB hunit i)
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  change ((B : M N).submatrix (pos sz i) (pos sz i)).det *
    ((B : M N).submatrix (pos sz i) (pos sz i)).det = 1 at h
  rcases mul_self_eq_one_iff.mp h with h | h <;> rw [h] <;> norm_num

private theorem abs_det_scaledAction (d : Fin c → ℝ) (hd : ∀ i, 0 < d i)
    (B : K N) (hB : BlockZero sz (B : M N)) (i j : Fin c) :
    |LinearMap.det (offBlockAction (scaledBlock sz d hd B hB i)
      (scaledBlock sz d hd B hB j)).toLinearMap| = (d j / d i) ^ (sz i * sz j) := by
  rw [det_offBlockAction, abs_mul, abs_pow, abs_pow, Fintype.card_fin, Fintype.card_fin]
  change |Matrix.det ((d i)⁻¹ • (B : M N).submatrix (pos sz i) (pos sz i))| ^ sz j *
    |Matrix.det (d j • ((B : M N).submatrix (pos sz j) (pos sz j))ᵀ)| ^ sz i = _
  rw [Matrix.det_smul, Matrix.det_smul, Matrix.det_transpose, abs_mul, abs_mul, abs_pow, abs_pow,
    Fintype.card_fin, Fintype.card_fin, abs_of_pos (inv_pos.mpr (hd i)), abs_of_pos (hd j),
    abs_det_orthogonal_block sz B hB i, abs_det_orthogonal_block sz B hB j, mul_one, mul_one,
    ← pow_mul, ← pow_mul, Nat.mul_comm (sz j) (sz i), ← mul_pow, div_eq_inv_mul]

/-- The ordered product of the normalized determinants for each pair of blocks. -/
def normalizedProduct (d : Fin c → ℝ) (hd : ∀ i, 0 < d i) (B : K N) (hB : BlockZero sz (B : M N)) : ℝ :=
  ∏ b : OffPair c, normalizedOffBlockDet (scaledBlock sz d hd B hB b.1.1)
    (scaledBlock sz d hd B hB b.1.2)

theorem abs_det_argument_eq_normalized (d : Fin c → ℝ) (hd : ∀ i, 0 < d i)
    (B W : K N) (hB : BlockZero sz (B : M N)) :
    |(argumentLowerEnd sz (d ∘ cls sz) B W).det| = borelWeight sz d * normalizedProduct sz d hd B hB := by
  rw [abs_det_argumentLowerEnd sz _ _ _ hB, realCartanTransverseDeterminant c sz d hd B hB,
    borelWeight_eq_product sz d hd, normalizedProduct, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun b _ => ?_
  unfold normalizedOffBlockDet rectangleDifference
  dsimp only
  rw [abs_det_scaledAction sz d hd B hB]
  have hpos : 0 < Real.sqrt ((d b.1.2 / d b.1.1) ^ (sz b.1.1 * sz b.1.2)) :=
    Real.sqrt_pos.2 (pow_pos (div_pos (hd _) (hd _)) _)
  field_simp [hpos.ne']

end Modulus

section Radial

variable {c : ℕ}

/-- The complex exponent of the block's determinant twist. -/
def blockTwist : RealBlock → ℂ
  | .character a => a.exponent
  | .induced a => a.exponent

/-- The product of the unshifted radial block weights. -/
def centralRadialProduct (b : Fin c → RealBlock) (d : Fin c → ℝ) : ℂ :=
  ∏ i, Complex.exp ((Real.log (d i) : ℂ) * ((blockSizes b i : ℂ) * blockTwist (b i)))

private theorem sum_blockExponents (b : RealBlock) :
    ∑ j : Fin b.rank, realPositionExponent [b] j = (b.rank : ℂ) * blockTwist b := by
  cases b with
  | character a => simp [RealBlock.rank, realPositionExponent, blockTwist]
  | induced a => simp [RealBlock.rank, Fin.sum_univ_two, realPositionExponent, blockTwist]; ring

private theorem product_exponent_eq (b : Fin c → RealBlock) (d : Fin c → ℝ) (hd : ∀ i, 0 < d i) :
    (∏ p : Fin (∑ i, blockSizes b i), (d (cls (blockSizes b) p) : ℂ) ^
      realPositionExponent (List.ofFn b) p) = centralRadialProduct b d := by
  rw [← finSigmaFinEquiv.prod_comp, Fintype.prod_sigma, centralRadialProduct]
  refine Finset.prod_congr rfl fun i _ => ?_
  change (∏ j : Fin (blockSizes b i), (d (cls (blockSizes b) (pos (blockSizes b) i j)) : ℂ) ^
    realPositionExponent (List.ofFn b) (pos (blockSizes b) i j)) = _
  simp_rw [cls_pos, exponent_pos, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (hd i).ne'),
    ← Complex.ofReal_log (hd i).le, ← Complex.exp_sum, ← Finset.mul_sum, sum_blockExponents]

theorem extension_eq_borel_mul_radial (b : Fin c → RealBlock) (d : Fin c → ℝ) (hd : ∀ i, 0 < d i)
    (g : G (∑ i, blockSizes b i)) (k : K (∑ i, blockSizes b i))
    (hg : (g : M (∑ i, blockSizes b i)) = diagonal (d ∘ cls (blockSizes b)) * (k : M (∑ i, blockSizes b i))) :
    extension (shiftedExponent (∑ i, blockSizes b i) (realPositionExponent (List.ofFn b))) 1 g =
      (borelWeight (blockSizes b) d : ℂ) * centralRadialProduct b d := by
  let n := ∑ i, blockSizes b i
  let a := d ∘ cls (blockSizes b)
  have ha (p : Fin n) : diagonal a p p ≠ 0 := by
    rw [diagonal_apply_eq]
    exact (hd (cls (blockSizes b) p)).ne'
  rw [extension_eq _ _ (blockTriangular_diagonal a) ha k.2 hg]
  simp only [Pi.one_apply, mul_one, diagonal_apply_eq, a, Function.comp_apply]
  simp_rw [abs_of_pos (hd _), shiftedExponent, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (hd _).ne')]
  rw [Finset.prod_mul_distrib, product_exponent_eq b d hd, mul_comm]
  congr 1
  unfold borelWeight
  push_cast
  exact Finset.prod_congr rfl fun p _ => by
    rw [Complex.ofReal_cpow (hd _).le]
    push_cast
    rfl

end Radial

/-- The determinant normalization and the actual radial weight use the same Borel half-density. -/
def RealCartanRadialWeightStatement : Prop :=
  (∀ (c : ℕ) (sz : Fin c → ℕ) (d : Fin c → ℝ) (hd : ∀ i, 0 < d i)
    (B W : K (∑ i, sz i)) (hB : BlockZero sz (B : M (∑ i, sz i))),
    |(argumentLowerEnd sz (d ∘ cls sz) B W).det| = borelWeight sz d * normalizedProduct sz d hd B hB) ∧
  (∀ (c : ℕ) (b : Fin c → RealBlock) (d : Fin c → ℝ), (∀ i, 0 < d i) →
    (∀ (g : G (∑ i, blockSizes b i)) (k : K (∑ i, blockSizes b i)),
      (g : M (∑ i, blockSizes b i)) = diagonal (d ∘ cls (blockSizes b)) * (k : M (∑ i, blockSizes b i)) →
      extension (shiftedExponent (∑ i, blockSizes b i) (realPositionExponent (List.ofFn b))) 1 g =
        (borelWeight (blockSizes b) d : ℂ) * centralRadialProduct b d))

theorem realCartanRadialWeight : RealCartanRadialWeightStatement :=
  ⟨fun _ => abs_det_argument_eq_normalized, fun _ => extension_eq_borel_mul_radial⟩

end Langlands.Archimedean.RealCartanRadialWeight
