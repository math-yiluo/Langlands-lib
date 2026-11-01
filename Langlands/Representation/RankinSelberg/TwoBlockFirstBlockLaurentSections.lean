import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockQuotientData
import Langlands.Representation.RankinSelberg.TwoBlockUnfoldingIntegrandData

/-!
# First-block coefficient functions of a two-block section

For an actual lower-induced section `f` of `σ_0 ⊗ σ_1` and functionals `ℓ_0, ℓ_1`, the
scalar section at `diag(v, 1) g` is the inverse half modulus of `diag(v, 1)` times the
value at `v` of the actual coefficient function of `σ_0` of the vector obtained by
contracting the second tensor factor of `f(g)` with `ℓ_1`. Lower radical translates do
not change these coefficient functions.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockFirstBlockLaurent

open GeneralLinear TwoBlockJacquet TwoBlockFirstBlockQuotient TwoBlockLowerUnipotentQuotient
  TwoBlockLowerFirstBlockQuotient Whittaker

universe uF uW

section Contraction

variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- Contraction of the second tensor factor against a functional. -/
def secondContraction (ell : W 1 →ₗ[ℂ] ℂ) : PiTensorProduct ℂ W →ₗ[ℂ] W 0 :=
  PiTensorProduct.lift
    { toFun := fun w => ell (w 1) • w 0
      map_update_add' := by
        intro _ w i x y
        fin_cases i <;> simp [smul_add, add_smul]
      map_update_smul' := by
        intro _ w i c x
        fin_cases i <;> simp [smul_smul, mul_comm] }

@[simp]
theorem secondContraction_tprod (ell : W 1 →ₗ[ℂ] ℂ) (w : ∀ i, W i) :
    secondContraction ell (PiTensorProduct.tprod ℂ w) = ell (w 1) • w 0 := by
  rw [secondContraction, PiTensorProduct.lift.tprod]
  rfl

end Contraction

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable {t : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)}

/-- Contraction against `ℓ_0 ⊗ ℓ_1` after acting by `diag(v, 1)` is `ℓ_0 (σ_0(v) y)`,
where `y` is the contraction of the second factor. -/
theorem tensorContraction_blockTensor_blockPair_one (ell : ∀ i, W i →ₗ[ℂ] ℂ)
    (v : GeneralLinear (m 0 + 1) F.Carrier) (X : PiTensorProduct ℂ W) :
    tensorContraction ell
        ((succBlockShape m h).blockTensor σ (blockPair F.Carrier (v, 1)) X) =
      ell 0 (σ 0 v (secondContraction (ell 1) X)) := by
  induction X using PiTensorProduct.induction_on with
  | smul_tprod c w =>
    rw [map_smul, map_smul, map_smul, BlockShape.blockTensor_tprod, tensorContraction_tprod,
      secondContraction_tprod, Fin.prod_univ_two, blockPair_apply_zero, blockPair_apply_one,
      map_one, Module.End.one_apply]
    simp only [map_smul, smul_eq_mul]
    ring
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add, map_add, map_add]

/-- The actual lower radical lies in the lower parabolic with trivial Levi projection,
so it leaves every scalar section unchanged. -/
theorem scalarSection_lowerRadical_mul (ell : ∀ i, W i →ₗ[ℂ] ℂ) (f : Sections F h σ)
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) (a : (succBlockShape m h).Levi F.Carrier) :
    scalarSection ell f (lowerRadical h F.Carrier Z * g) a = scalarSection ell f g a := by
  let q : (succBlockShape m h).oppositeParabolic F.Carrier :=
    Subgroup.inclusion (lowerBlockUnipotent_le_oppositeParabolic h F.Carrier)
      ⟨lowerRadical h F.Carrier Z, lowerRadical_mem h F.Carrier Z⟩
  have hq : (succBlockShape m h).oppositeLeviProjection F.Carrier q = 1 := by
    funext i
    apply Units.ext
    ext a b
    rw [BlockShape.oppositeLeviProjection_apply]
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · change lowerRadical h F.Carrier Z ((succBlockShape m h).index 0 a)
        ((succBlockShape m h).index 0 b) = (1 : Matrix _ _ F.Carrier) a b
      rw [lowerRadical_index_zero_zero, Matrix.one_apply]
    · change lowerRadical h F.Carrier Z ((succBlockShape m h).index 1 a)
        ((succBlockShape m h).index 1 b) = (1 : Matrix _ _ F.Carrier) a b
      rw [lowerRadical_index_one_one, Matrix.one_apply]
  have hcov := scalarSection_covariant ell f q hq g a
  rw [map_one, Units.val_one, inv_one, one_mul, mul_one] at hcov
  exact hcov

variable {ψ : letI := F.canonicalTopologicalData.topology
  HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier}

/-- The first-block coefficient function `v ↦ ℓ_0(σ_0(v) y)` of the contracted value
`y = (1 ⊗ ℓ_1) f(g)`, as an element of the actual coefficient image of `σ_0`. -/
def firstBlockCoefficient
    (ell : letI := F.canonicalTopologicalData.topology
      ∀ i, glInverseFunctionals ψ (m i) (σ i))
    (f : Sections F h σ) (g : GeneralLinear (t + 1) F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    (coefficientModel (σ 0) (ell 0)).toSubmodule :=
  letI := F.canonicalTopologicalData.topology
  modelMap (σ 0) (ell 0) (secondContraction (ell 1).val (sectionEval F h σ f g))

theorem firstBlockCoefficient_apply
    (ell : letI := F.canonicalTopologicalData.topology
      ∀ i, glInverseFunctionals ψ (m i) (σ i))
    (f : Sections F h σ) (g : GeneralLinear (t + 1) F.Carrier)
    (v : GeneralLinear (m 0 + 1) F.Carrier) :
    (firstBlockCoefficient ell f g).val.val v =
      scalarSection (fun i => (ell i).val) f g (blockPair F.Carrier (v, 1)) := by
  rw [scalarSection_def, tensorContraction_blockTensor_blockPair_one]
  rfl

/-- Lower radical translates have the same first-block coefficient function. -/
theorem firstBlockCoefficient_lowerRadical_mul
    (ell : letI := F.canonicalTopologicalData.topology
      ∀ i, glInverseFunctionals ψ (m i) (σ i))
    (f : Sections F h σ) (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) :
    firstBlockCoefficient ell f (lowerRadical h F.Carrier Z * g) =
      firstBlockCoefficient ell f g := by
  apply Subtype.ext
  apply Subtype.ext
  funext v
  rw [firstBlockCoefficient_apply, firstBlockCoefficient_apply, scalarSection_lowerRadical_mul]

/-- The scalar section at `diag(v, 1) g` is the inverse half modulus of `diag(v, 1)`
times the first-block coefficient function at `v`. -/
theorem scalarSection_firstBlockEmbedding_mul
    (ell : letI := F.canonicalTopologicalData.topology
      ∀ i, glInverseFunctionals ψ (m i) (σ i))
    (f : Sections F h σ) (v : GeneralLinear (m 0 + 1) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) :
    scalarSection (fun i => (ell i).val) f (firstBlockEmbedding h F.Carrier v * g) 1 =
      ((F.canonicalTopologicalData.leviHalfModulus (succBlockShape m h)
          (blockPair F.Carrier (v, 1)) : ℂˣ) : ℂ)⁻¹ *
        (firstBlockCoefficient ell f g).val.val v := by
  have hcov := scalarSection_covariant (fun i => (ell i).val) f
    ((succBlockShape m h).oppositeLeviInParabolic F.Carrier (blockPair F.Carrier (v, 1)))
    (BlockShape.oppositeLeviProjection_section _ _ _) g 1
  rw [one_mul] at hcov
  rw [firstBlockCoefficient_apply]
  exact hcov

open scoped NNReal in
/-- The inverse half modulus of `diag(v, 1)` is the determinant weight `|det v|^(-b/2)`. -/
theorem inv_leviHalfModulus_blockPair_one (v : GeneralLinear (m 0 + 1) F.Carrier) :
    ((F.canonicalTopologicalData.leviHalfModulus (succBlockShape m h)
        (blockPair F.Carrier (v, 1)) : ℂˣ) : ℂ)⁻¹ =
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) v
        (-(((m 1 + 1 : ℕ) : ℂ) / 2)) := by
  set T := F.canonicalTopologicalData
  set r : ℝ := T.normalizedAbs (GeneralLinear.determinant v : F.Carrier) with hr_def
  have hr : 0 < r := T.normalizedAbs_pos (GeneralLinear.determinant v).ne_zero
  have hlm : ((T.leviModulus (succBlockShape m h) (blockPair F.Carrier (v, 1)) : ℝ≥0) : ℝ) =
      r ^ (m 1 + 1) := by
    rw [T.leviModulus_apply]
    simp only [Finset.prod_filter, Fin.prod_univ_two]
    simp only [Fin.isValue, lt_self_iff_false, ite_false, Fin.zero_lt_one, ite_true,
      not_lt_zero, mul_one, one_mul]
    rw [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
      NNReal.coe_div, NNReal.coe_pow, NNReal.coe_pow]
    change ((T.determinantNorm (m 0 + 1) (blockPair F.Carrier (v, 1) 0) : ℝ≥0) : ℝ) ^ (m 1 + 1) /
      ((T.determinantNorm (m 1 + 1) (blockPair F.Carrier (v, 1) 1) : ℝ≥0) : ℝ) ^ (m 0 + 1) = _
    rw [blockPair_apply_zero, blockPair_apply_one, map_one, Units.val_one, NNReal.coe_one,
      one_pow, div_one]
    rfl
  have hsqrt : Real.sqrt (r ^ (m 1 + 1)) = r ^ ((((m 1 + 1 : ℕ) : ℝ)) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    congr 1
    ring
  rw [T.leviHalfModulus_apply, Real.coe_sqrt, hlm, hsqrt, determinantWeight]
  change ((r ^ ((((m 1 + 1 : ℕ) : ℝ)) / 2) : ℝ) : ℂ)⁻¹ = (r : ℂ) ^ (-(((m 1 + 1 : ℕ) : ℂ) / 2))
  rw [← Complex.ofReal_inv, ← Real.rpow_neg hr.le, Complex.ofReal_cpow hr.le]
  push_cast
  ring_nf

end Langlands.RankinSelberg.TwoBlockFirstBlockLaurent
