import Langlands.Representation.RankinSelberg.UnequalRankCharacterChange
import Langlands.Representation.RankinSelberg.UnequalRankBlockZeroCovariance
import Langlands.Representation.RankinSelberg.TwoBlockDominantGammaDuality
import Langlands.Representation.Classification.ConstituentCompatibility

/-!
# The dual unequal-rank integral under change of additive character

For `ψ^a(x) = ψ(ax)` and the transported functionals `v ↦ ℓ(π(D) v)`,
`u ↦ ℓ'(σ(d_a) u)`, the transformed (dual) unequal-rank integral of block
`(k, j)` for `ψ^a` is a fixed nonzero monomial in `q^(-s)` times the transformed
integral for `ψ` of the vectors `π(R) v` and `u`, where `R` is the fixed right
correction of the forward change of variables. The central characters of `π`
and `σ` enter through the scalar matrices relating the two dual vectors.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
open scoped NNReal

universe uF uV uW

section Matrices

variable {F : Type uF} [Field F]

/-- The right correction `diag(a^(r-n) I_(n+1), a^(r-n-1), ..., a, 1)` in
`GL_(r+1)(F)`, for an arbitrary large rank `r`. -/
def blockCorrectionAt (a : Fˣ) (n r : ℕ) : Langlands.GeneralLinear (r + 1) F where
  val := Matrix.diagonal fun i =>
    ((a ^ (if i.val < n + 1 then r - n else r - i.val) : Fˣ) : F)
  inv := Matrix.diagonal fun i =>
    (((a ^ (if i.val < n + 1 then r - n else r - i.val))⁻¹ : Fˣ) : F)
  val_inv := by simp [Matrix.diagonal_mul_diagonal]
  inv_val := by simp [Matrix.diagonal_mul_diagonal]

@[simp] theorem blockCorrectionAt_val (a : Fˣ) (n r : ℕ) :
    (blockCorrectionAt a n r : Langlands.GeneralLinear (r + 1) F).val =
      Matrix.diagonal fun i =>
        ((a ^ (if i.val < n + 1 then r - n else r - i.val) : Fˣ) : F) := rfl

@[simp] theorem blockCorrectionAt_inv_val (a : Fˣ) (n r : ℕ) :
    (blockCorrectionAt a n r : Langlands.GeneralLinear (r + 1) F)⁻¹.val =
      Matrix.diagonal fun i =>
        (((a ^ (if i.val < n + 1 then r - n else r - i.val))⁻¹ : Fˣ) : F) := rfl

/-- At `r = n + d` the correction is the published block correction. -/
theorem blockCorrectionAt_add (a : Fˣ) (n d : ℕ) :
    blockCorrectionAt a n (n + d) = (characterChangeBlockCorrection a n d :
      Langlands.GeneralLinear (n + d + 1) F) := by
  apply Units.ext
  change Matrix.diagonal _ = Matrix.diagonal _
  simp only [Nat.add_sub_cancel_left]

/-- The inverse transpose of an invertible matrix with diagonal inverse is its
inverse. -/
theorem inverseTranspose_of_diagonal {m : ℕ} (g : Langlands.GeneralLinear m F)
    (f : Fin m → F) (hg : (g⁻¹).val = Matrix.diagonal f) :
    inverseTranspose m F g = g⁻¹ := by
  apply Units.ext
  rw [inverseTranspose_coe, hg, Matrix.diagonal_transpose]

/-- The inverse transpose of `d_a` is `d_a⁻¹`. -/
theorem inverseTranspose_characterChangeElement (a : Fˣ) (m : ℕ) :
    inverseTranspose (m + 1) F (characterChangeElement a m) =
      (characterChangeElement a m)⁻¹ :=
  inverseTranspose_of_diagonal _ _ (characterChangeElement_inv_val a m)

/-- The inverse transpose of `R⁻¹` is `R`. -/
theorem inverseTranspose_blockCorrectionAt_inv (a : Fˣ) (n r : ℕ) :
    inverseTranspose (r + 1) F (blockCorrectionAt a n r)⁻¹ = blockCorrectionAt a n r := by
  rw [inverseTranspose_of_diagonal _ _ (by rw [inv_inv]; exact blockCorrectionAt_val a n r),
    inv_inv]

/-- The inverse transpose of the scalar matrix `c` is the scalar matrix `c⁻¹`. -/
theorem inverseTranspose_scalar' (m : ℕ) (c : Fˣ) :
    inverseTranspose m F (Matrix.GeneralLinearGroup.scalar (Fin m) c) =
      Matrix.GeneralLinearGroup.scalar (Fin m) c⁻¹ := by
  rw [inverseTranspose_of_diagonal _ (fun _ => ((c⁻¹ : Fˣ) : F)), ← map_inv]
  rw [← map_inv]
  rfl

/-- Conjugating `d_a⁻¹` by the long Weyl element gives `a^(-m) d_a`. -/
theorem weylLong_conj_characterChangeElement_inv (a : Fˣ) (m : ℕ) :
    weylLong (m + 1) F * (characterChangeElement a m)⁻¹ * weylLong (m + 1) F =
      (Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (a ^ m))⁻¹ *
        characterChangeElement a m := by
  apply Units.ext
  ext i j
  rw [weylLong_conjugate_entry]
  change ((characterChangeElement a m)⁻¹).val i.rev j.rev =
    ((Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (a ^ m))⁻¹.val *
      (characterChangeElement a m).val) i j
  rw [← map_inv, characterChangeElement_inv_val, characterChangeElement_val,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_apply, Matrix.diagonal_apply]
  simp only [Fin.rev_inj]
  split_ifs with h
  · subst h
    rw [Fin.val_rev]
    have hi : m + 1 - (m + 1 - (i.val + 1)) = i.val + 1 := by omega
    have hpow : (a : F) ^ m = (a : F) ^ i.val * (a : F) ^ (m - i.val) := by
      rw [← pow_add]
      congr 1
      omega
    simp only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    rw [show m - (m + 1 - (i.val + 1)) = i.val by omega, hpow]
    have ha : (a : F) ≠ 0 := a.ne_zero
    field_simp
  · rfl

/-- The long Weyl element moves past `d_a⁻¹` at the cost of the scalar `a^(-m)`. -/
theorem weylLong_mul_characterChangeElement_inv (a : Fˣ) (m : ℕ) :
    weylLong (m + 1) F * (characterChangeElement a m)⁻¹ =
      (Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (a ^ m))⁻¹ *
        characterChangeElement a m * weylLong (m + 1) F := by
  rw [← weylLong_conj_characterChangeElement_inv, mul_assoc _ (weylLong (m + 1) F),
    weylLong_mul_self, mul_one]

variable {n r : ℕ}

/-- Scalar matrices are central. -/
theorem scalar_mul_comm' {m : ℕ} (c : Fˣ) (g : Langlands.GeneralLinear m F) :
    Matrix.GeneralLinearGroup.scalar (Fin m) c * g =
      g * Matrix.GeneralLinearGroup.scalar (Fin m) c := by
  apply Units.ext
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
  exact (Matrix.scalar_commute _ (Commute.all _) _).eq

/-- The block matrix `diag(b I_(n+1), I_(r-n))` of the translation law is diagonal. -/
theorem appendScalar_val (b : Fˣ) (hnr : n < r) :
    (GeneralLinear.reindex (finCongr (show n + (r - n) + 1 = r + 1 by omega))
        (appendIdentity n (r - n) (Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) b)) :
          Langlands.GeneralLinear (r + 1) F).val =
      Matrix.diagonal fun i => if i.val < n + 1 then (b : F) else 1 := by
  ext i j
  change (appendIdentity n (r - n) (Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) b))
    (Fin.cast (by omega) i) (Fin.cast (by omega) j) = _
  rw [appendIdentity_entry, Matrix.diagonal_apply]
  simp only [Fin.val_cast, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

open UnequalRankComplementaryConjugationProof in
/-- Conjugating a diagonal matrix by the block Weyl element permutes its
entries by the tail reversal. -/
theorem blockWeylAt_conj_val (hnr : n < r) (g : Langlands.GeneralLinear (r + 1) F)
    (f : Fin (r + 1) → F) (hg : g.val = Matrix.diagonal f) :
    (blockWeylAt n r hnr * g * blockWeylAt n r hnr).val =
      Matrix.diagonal (f ∘ tailRev n r) := by
  rw [blockWeylAt_eq]
  ext i j
  change ((permutation (r + 1) F (tailRevPerm n r) * g) * permutation (r + 1) F
    (tailRevPerm n r)) i j = _
  rw [mul_permutation_entry, permutation_mul_entry]
  rw [hg, Matrix.diagonal_apply, Matrix.diagonal_apply]
  have hinv : (tailRevPerm n r)⁻¹ i = tailRev n r i := rfl
  have hj : (tailRevPerm n r) j = tailRev n r j := rfl
  simp only [hinv, hj, (tailRev_involutive n r).injective.eq_iff]
  rfl

/-- The scalar identity `w' R w' E R = a^(r-n-1)` relating the forward and the
dual corrections, with `E = diag(a^(-(r-n+1)) I_(n+1), I_(r-n))`. -/
theorem blockWeylAt_blockCorrectionAt_scalar (a : Fˣ) (hnr : n < r) :
    blockWeylAt n r hnr * blockCorrectionAt a n r * blockWeylAt n r hnr *
        GeneralLinear.reindex (finCongr (show n + (r - n) + 1 = r + 1 by omega))
          (appendIdentity n (r - n)
            (Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) (a ^ (r - n + 1))⁻¹)) *
        blockCorrectionAt a n r =
      Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) (a ^ (r - n - 1)) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, blockWeylAt_conj_val hnr _ _ (blockCorrectionAt_val a n r),
    appendScalar_val _ hnr, blockCorrectionAt_val, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.GeneralLinearGroup.coe_scalar]
  change _ = Matrix.diagonal fun _ => _
  congr 1
  funext i
  have ha : (a : F) ≠ 0 := a.ne_zero
  simp only [Function.comp_apply, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
  by_cases hi : i.val < n + 1
  · rw [UnequalRankComplementaryConjugationProof.tailRev_of_lt n r hi]
    simp only [hi, ↓reduceIte, Pi.constRingHom_apply, Function.const_apply]
    have h1 : r - n = (r - n - 1) + 1 := by omega
    rw [show r - n + 1 = (r - n - 1) + 2 by omega, h1]
    simp only [Nat.add_sub_cancel]
    field_simp
    ring
  · have hv := UnequalRankComplementaryConjugationProof.tailRev_val_of_ge n r hi
    have hi'' : ¬ (r + n + 1 - i.val < n + 1) := by omega
    simp only [hi, hi'', ↓reduceIte, hv, mul_one, Pi.constRingHom_apply, Function.const_apply]
    rw [← pow_add]
    congr 1
    omega

/-- The inverse transpose commutes with right translation by the block Weyl element. -/
theorem inverseTranspose_mul_blockWeylAt (hnr : n < r) (g : Langlands.GeneralLinear (r + 1) F) :
    inverseTranspose (r + 1) F (g * blockWeylAt n r hnr) =
      inverseTranspose (r + 1) F g * blockWeylAt n r hnr := by
  rw [map_mul, DominantRankTransport.inverseTranspose_blockWeylAt]

/-- The matrix identity behind the dual side: with `D = d_a` of rank `r`, the
correction `R` and `E = diag(a^(-(r-n+1)) I_(n+1), I_(r-n))`,
`w ι(D g R⁻¹ w') E R = a^(-(n+1)) D w ι(g w')`. -/
theorem weylLong_inverseTranspose_correction (a : Fˣ) (hnr : n < r)
    (g : Langlands.GeneralLinear (r + 1) F) :
    weylLong (r + 1) F * inverseTranspose (r + 1) F
        (characterChangeElement a r * g * (blockCorrectionAt a n r)⁻¹ *
          blockWeylAt n r hnr) *
        GeneralLinear.reindex (finCongr (show n + (r - n) + 1 = r + 1 by omega))
          (appendIdentity n (r - n)
            (Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) (a ^ (r - n + 1))⁻¹)) *
        blockCorrectionAt a n r =
      (Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) (a ^ (n + 1)))⁻¹ *
        (characterChangeElement a r *
          (weylLong (r + 1) F * inverseTranspose (r + 1) F (g * blockWeylAt n r hnr))) := by
  set w' := blockWeylAt (F := F) n r hnr
  set E := GeneralLinear.reindex (finCongr (show n + (r - n) + 1 = r + 1 by omega))
    (appendIdentity n (r - n)
      (Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) (a ^ (r - n + 1))⁻¹))
  set R := blockCorrectionAt a n r
  set D := characterChangeElement a r
  have key : R * w' * E * R =
      w' * Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) (a ^ (r - n - 1)) := by
    rw [← blockWeylAt_blockCorrectionAt_scalar a hnr]
    simp only [← mul_assoc, w', DominantRankTransport.blockWeylAt_mul_self, one_mul]
    rfl
  have hsc : (Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) (a ^ r))⁻¹ *
      Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) (a ^ (r - n - 1)) =
      (Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) (a ^ (n + 1)))⁻¹ := by
    rw [← map_inv, ← map_inv, ← map_mul]
    congr 1
    rw [show r = (n + 1) + (r - n - 1) by omega, pow_add]
    rw [show (n + 1) + (r - n - 1) - n - 1 = r - n - 1 by omega]
    group
  rw [map_mul, map_mul, map_mul, inverseTranspose_characterChangeElement,
    inverseTranspose_blockCorrectionAt_inv, DominantRankTransport.inverseTranspose_blockWeylAt]
  calc weylLong (r + 1) F * (D⁻¹ * inverseTranspose (r + 1) F g * R * w') * E * R
      = (weylLong (r + 1) F * D⁻¹) * inverseTranspose (r + 1) F g * (R * w' * E * R) := by
        simp only [mul_assoc]
    _ = (Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) (a ^ r))⁻¹ * D * weylLong (r + 1) F *
          inverseTranspose (r + 1) F g *
          (w' * Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) (a ^ (r - n - 1))) := by
        rw [key, weylLong_mul_characterChangeElement_inv]
    _ = (Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) (a ^ r))⁻¹ *
          ((D * (weylLong (r + 1) F * (inverseTranspose (r + 1) F g * w'))) *
            Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) (a ^ (r - n - 1))) := by
        simp only [mul_assoc]
    _ = (Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) (a ^ r))⁻¹ *
          (Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) (a ^ (r - n - 1)) *
            (D * (weylLong (r + 1) F * (inverseTranspose (r + 1) F g * w')))) := by
        rw [scalar_mul_comm' (a ^ (r - n - 1))]
    _ = _ := by
        rw [← mul_assoc, hsc]
        simp only [w', inverseTranspose_mul_blockWeylAt]

end Matrices

section Measures

/-- A product of copies of `c • m` is `c ^ card ι` times the product of copies of `m`. -/
theorem measure_pi_const_smul {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (m : Measure α) [SigmaFinite m] (c : ℝ≥0) :
    Measure.pi (fun _ : ι => c • m) = (c ^ Fintype.card ι) • Measure.pi (fun _ : ι => m) := by
  apply Measure.pi_eq
  intro s _
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, ENNReal.coe_pow]

variable {F : Type uF} [AddGroup F] [TopologicalSpace F] [MeasurableSpace F]

/-- If `ν' = κ ν`, the rectangular product measures differ by `κ^(j t)`. -/
theorem rectangularMeasure_eq_smul {ν ν' : AdditiveHaarMeasure F} [SigmaFinite ν.measure]
    (κ : ℝ≥0) (h : ν'.measure = κ • ν.measure) (j t : ℕ) :
    rectangularMeasure ν' j t = (κ ^ (j * t)) • rectangularMeasure ν j t := by
  unfold rectangularMeasure
  rw [h, measure_pi_const_smul, measure_pi_const_smul, Fintype.card_fin, Fintype.card_fin,
    ← pow_mul, mul_comm t j]
  rfl

end Measures

section Integrals

variable {F : Type uF} [Field F] [TopologicalSpace F] {n r : ℕ}
  (abv : AbsoluteValue F ℝ) (j k : ℕ)
  [MeasurableSpace (LeftUnipotentQuotient n F)] [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
  (μ : Measure (LeftUnipotentQuotient n F))

/-- The unequal-rank integral under an equality of characters, a scalar multiple
of the rectangular measure, and pointwise scalar multiples of both functions. -/
theorem unequalRankIntegral_congr_smul {ψ₁ ψ₂ : UnitaryAdditiveCharacter F} (hψ : ψ₁ = ψ₂)
    {ρ₁ ρ₂ : Measure (Matrix (Fin j) (Fin (n + 1)) F)} (κ : ℝ≥0) (hρ : ρ₂ = κ • ρ₁)
    {W₁ : WhittakerFunctions ψ₁ (n + (j + k + 1))} {W₂ : WhittakerFunctions ψ₂ (n + (j + k + 1))}
    {W₁' : InverseWhittakerFunctions ψ₁ n} {W₂' : InverseWhittakerFunctions ψ₂ n}
    (c c' : ℂ) (hW : ∀ g, W₂.val g = c * W₁.val g) (hW' : ∀ g, W₂'.val g = c' * W₁'.val g)
    (s : ℂ) :
    unequalRankIntegral ψ₂ abv j k μ ρ₂ W₂ W₂' s =
      ((κ : ℝ) : ℂ) * c * c' * unequalRankIntegral ψ₁ abv j k μ ρ₁ W₁ W₁' s := by
  subst hψ hρ
  have he : ∀ x q, unequalRankIntegrand ψ₁ abv j k W₂ W₂' s x q =
      c * c' * unequalRankIntegrand ψ₁ abv j k W₁ W₁' s x q := by
    intro x q
    induction q using Quotient.inductionOn with
    | h g =>
      simp only [unequalRankIntegrand_mk, hW, hW']
      ring
  unfold unequalRankIntegral
  simp only [he, integral_smul_nnreal_measure, integral_const_mul, NNReal.smul_def,
    Complex.real_smul]
  ring

end Integrals

section IntegralsAt

variable {F : Type uF} [Field F] [TopologicalSpace F] [MeasurableSpace F] {n r : ℕ}
  (abv : AbsoluteValue F ℝ) (j k : ℕ)
  [MeasurableSpace (LeftUnipotentQuotient n F)] (μ : Measure (LeftUnipotentQuotient n F))

/-- The transported version of `unequalRankIntegral_congr_smul`. -/
theorem unequalRankIntegralAt_congr_smul (hr : r = n + (j + k + 1))
    {ψ₁ ψ₂ : UnitaryAdditiveCharacter F} (hψ : ψ₁ = ψ₂)
    {ρ₁ ρ₂ : Measure (Matrix (Fin j) (Fin (n + 1)) F)} (κ : ℝ≥0) (hρ : ρ₂ = κ • ρ₁)
    {W₁ : WhittakerFunctions ψ₁ r} {W₂ : WhittakerFunctions ψ₂ r}
    {W₁' : InverseWhittakerFunctions ψ₁ n} {W₂' : InverseWhittakerFunctions ψ₂ n}
    (c c' : ℂ) (hW : ∀ g, W₂.val g = c * W₁.val g) (hW' : ∀ g, W₂'.val g = c' * W₁'.val g)
    (s : ℂ) :
    unequalRankIntegralAt j k hr ψ₂ abv μ ρ₂ W₂ W₂' s =
      ((κ : ℝ) : ℂ) * c * c' * unequalRankIntegralAt j k hr ψ₁ abv μ ρ₁ W₁ W₁' s := by
  subst hr
  exact unequalRankIntegral_congr_smul abv j k μ hψ κ hρ c c' hW hW' s

end IntegralsAt

section CharacterChangeAt

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

/-- The corrected large-rank Whittaker function `g ↦ W(D g R⁻¹)` at an arbitrary
large rank `r`, with `D = d_a` and `R = blockCorrectionAt a n r`. -/
def characterChangeFunctionAt (ψ : UnitaryAdditiveCharacter F) (a : Fˣ) (n r : ℕ)
    (W : WhittakerFunctions ψ r) : WhittakerFunctions (ψ.scale a) r :=
  functionRepresentation (upperUnipotent (r + 1) F) (standardCharacter (ψ.scale a) r)
    (blockCorrectionAt a n r)⁻¹ (characterChangeFunction ψ r a W)

@[simp] theorem characterChangeFunctionAt_apply (ψ : UnitaryAdditiveCharacter F) (a : Fˣ)
    (n r : ℕ) (W : WhittakerFunctions ψ r) (g : Langlands.GeneralLinear (r + 1) F) :
    (characterChangeFunctionAt ψ a n r W).val g =
      W.val (characterChangeElement a r * g * (blockCorrectionAt a n r)⁻¹) := by
  change W.val (characterChangeElement a r * (g * (blockCorrectionAt a n r)⁻¹)) = _
  rw [mul_assoc]

/-- At `r = n + (j + k + 1)` the corrected function is the published
`unequalRankCharacterChangeFunction`. -/
theorem characterChangeFunctionAt_add (ψ : UnitaryAdditiveCharacter F) (a : Fˣ) (n j k : ℕ)
    (W : WhittakerFunctions ψ (n + (j + k + 1))) :
    characterChangeFunctionAt ψ a n (n + (j + k + 1)) W =
      unequalRankCharacterChangeFunction ψ a n j k W := by
  apply Subtype.ext
  funext g
  rw [characterChangeFunctionAt_apply, unequalRankCharacterChangeFunction_apply,
    blockCorrectionAt_add]

variable [MeasurableSpace F] (q : ℕ) (hq : 0 < q) (ψ : UnitaryAdditiveCharacter F)
  (abv : AbsoluteValue F ℝ) (a : Fˣ) {n r : ℕ} (j k : ℕ)
  [MeasurableSpace (LeftUnipotentQuotient n F)] [BorelSpace (LeftUnipotentQuotient n F)]
  [BorelSpace (Matrix (Fin j) (Fin (n + 1)) F)]
  (μ : Measure (LeftUnipotentQuotient n F)) (ρ : Measure (Matrix (Fin j) (Fin (n + 1)) F))
  (hμ : HasCharacterChangeMeasureLaw abv a μ)
  (hρ : HasCharacterChangeRectangularMeasureLaw abv a j n ρ)
  (e : ℤ) (he : abv (Matrix.det (characterChangeElement a n).val) = (q : ℝ) ^ (-e))

include hq hμ hρ he in
/-- The forward change of character for the transported integral. -/
theorem unequalRankIntegralAt_characterChange (hr : r = n + (j + k + 1))
    (W : WhittakerFunctions ψ r) (W' : InverseWhittakerFunctions ψ n) (s : ℂ) :
    unequalRankIntegralAt j k hr (ψ.scale a) abv μ ρ
        (characterChangeFunctionAt ψ a n r W) (characterChangeInverseFunction ψ n a W') s =
      (unequalRankCharacterChangeScalar abv a n j k : ℂ) * spectralPoint q s ^ (-e) *
        unequalRankIntegralAt j k hr ψ abv μ ρ W W' s := by
  subst hr
  change unequalRankIntegral (ψ.scale a) abv j k μ ρ _ _ s =
    _ * unequalRankIntegral ψ abv j k μ ρ W W' s
  rw [characterChangeFunctionAt_add]
  exact unequalRankIntegral_characterChange_monomial q hq ψ abv a j k μ ρ hμ hρ e he W W' s

end CharacterChangeAt

section DualTranslate

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [MeasurableSpace F]
  {n r : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  (μ : Measure (LeftUnipotentQuotient n F))

/-- JPSS (2.11.2) for the inverse-transpose block `(k, j)` of the dual model
functions, for an arbitrary second block `j`: simultaneous right translation of
the original functions by `diag(g, I)` and `g`. -/
theorem dualIntegralAt_translate' [BorelSpace (LeftUnipotentQuotient n F)]
    (hnr : n < r) {j k : ℕ} (hr : r = n + (k + j + 1))
    {ρ : Measure (Matrix (Fin k) (Fin (n + 1)) F)}
    (hμ : ∀ g, MeasurePreserving (rightTranslate (upperUnipotent (n + 1) F) g) μ μ)
    (g : Langlands.GeneralLinear (n + 1) F)
    (hρ : ∀ G : Matrix (Fin k) (Fin (n + 1)) F → ℂ,
      ∫ x, G (x * (inverseTranspose (n + 1) F g).val) ∂ρ =
        determinantWeight abv (inverseTranspose (n + 1) F g) (-(k : ℂ)) * ∫ x, G x ∂ρ)
    {W₁ W₂ : WhittakerFunctions ψ r} {W₁' W₂' : InverseWhittakerFunctions ψ n}
    (hW : ∀ h, W₂.val h = W₁.val (h * GeneralLinear.reindex
      (finCongr (show n + (r - n) + 1 = r + 1 by omega)) (appendIdentity n (r - n) g)))
    (hW' : ∀ h, W₂'.val h = W₁'.val (h * g)) (s : ℂ) :
    unequalRankIntegralAt k j hr (ψ.scale (-1)) abv μ ρ
        (translateWhittaker (ψ.scale (-1)) r (firstDualFunction ψ r W₂) (blockWeylAt n r hnr))
        (secondDualFunction ψ n W₂') s =
      determinantWeight abv (inverseTranspose (n + 1) F g)
          (((k + j + 1 : ℕ) : ℂ) / 2 - s - k) *
        unequalRankIntegralAt k j hr (ψ.scale (-1)) abv μ ρ
          (translateWhittaker (ψ.scale (-1)) r (firstDualFunction ψ r W₁) (blockWeylAt n r hnr))
          (secondDualFunction ψ n W₁') s := by
  refine unequalRankIntegralAt_translate (ψ.scale (-1)) abv μ hr hμ
    (inverseTranspose (n + 1) F g) hρ (fun h => ?_) (fun h => ?_) s
  · rw [translateWhittaker_apply, translateWhittaker_apply, firstDualFunction_apply,
      firstDualFunction_apply, hW, mul_assoc, inverseTranspose_mul_embedding hnr]
  · rw [secondDualFunction_apply, secondDualFunction_apply, hW', mul_assoc, map_mul,
      inverseTranspose_involutive]

end DualTranslate

section ModelFunctions

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {n r : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (ψ : UnitaryAdditiveCharacter F) (a : Fˣ)
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
  (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ)

/-- The model function of `v` for the translated functional `ℓ ∘ π(D)` is the
corrected function of `π(R) v` for `ℓ`. -/
theorem modelMap_characterChangeFunctional (v : V) :
    (modelMap π (characterChangeFunctional ψ π a ℓ) v).val =
      characterChangeFunctionAt ψ a n r (modelMap π ℓ (π (blockCorrectionAt a n r) v)).val := by
  apply Subtype.ext
  funext g
  rw [characterChangeFunctionAt_apply]
  change ℓ.val (π (characterChangeElement a r) (π g v)) =
    ℓ.val (π (characterChangeElement a r * g * (blockCorrectionAt a n r)⁻¹)
      (π (blockCorrectionAt a n r) v))
  rw [← Module.End.mul_apply (π (characterChangeElement a r * g * _)), ← map_mul,
    inv_mul_cancel_right, map_mul, Module.End.mul_apply]

/-- The model function of `u` for the translated functional `ℓ' ∘ σ(d_a)` is the
left translate by `d_a` of the model function of `u` for `ℓ'`. -/
theorem modelMap_characterChangeInverseFunctional (u : W) :
    (modelMap σ (characterChangeInverseFunctional ψ σ a ℓ') u).val =
      characterChangeInverseFunction ψ n a (modelMap σ ℓ' u).val := by
  apply Subtype.ext
  funext g
  change ℓ'.val (σ (characterChangeElement a n) (σ g u)) =
    ℓ'.val (σ (characterChangeElement a n * g) u)
  rw [map_mul, Module.End.mul_apply]

variable (ωπ ωσ : Fˣ →* ℂˣ)

/-- The first dual function of the translated model, translated by the block Weyl
element, is `ω_π(a)^(n+1)` times the corrected dual function of
`π(E) π(R) v` for `ψ^(-1)`, with `E = diag(a^(-(r-n+1)) I_(n+1), I_(r-n))`. -/
theorem firstDual_modelMap_characterChangeFunctional
    (hπ : Classification.HasGLCentralCharacter F (r + 1) π ωπ) (hnr : n < r) (v : V)
    (h : Langlands.GeneralLinear (r + 1) F) :
    (translateWhittaker ((ψ.scale a).scale (-1)) r
        (firstDualFunction (ψ.scale a) r (modelMap π (characterChangeFunctional ψ π a ℓ) v).val)
        (blockWeylAt n r hnr)).val h =
      ((ωπ a : ℂˣ) : ℂ) ^ (n + 1) *
        (characterChangeFunctionAt (ψ.scale (-1)) a n r
          (translateWhittaker (ψ.scale (-1)) r
            (firstDualFunction ψ r (modelMap π ℓ
              (π (GeneralLinear.reindex (finCongr (show n + (r - n) + 1 = r + 1 by omega))
                (appendIdentity n (r - n)
                  (Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) (a ^ (r - n + 1))⁻¹)))
                (π (blockCorrectionAt a n r) v))).val)
            (blockWeylAt n r hnr))).val h := by
  rw [characterChangeFunctionAt_apply, translateWhittaker_apply, translateWhittaker_apply,
    firstDualFunction_apply, firstDualFunction_apply]
  change ℓ.val (π (characterChangeElement a r)
      (π (weylLong (r + 1) F * inverseTranspose (r + 1) F (h * blockWeylAt n r hnr)) v)) =
    _ * ℓ.val (π (weylLong (r + 1) F * inverseTranspose (r + 1) F
      (characterChangeElement a r * h * (blockCorrectionAt a n r)⁻¹ * blockWeylAt n r hnr))
      (π (GeneralLinear.reindex (finCongr (show n + (r - n) + 1 = r + 1 by omega))
        (appendIdentity n (r - n)
          (Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) (a ^ (r - n + 1))⁻¹)))
        (π (blockCorrectionAt a n r) v)))
  have hm := congrArg (fun g => π g v) (weylLong_inverseTranspose_correction a hnr h)
  simp only [map_mul, Module.End.mul_apply] at hm
  simp only [map_mul, Module.End.mul_apply]
  rw [hm, ← map_inv (Matrix.GeneralLinearGroup.scalar (Fin (r + 1))), hπ, map_smul, smul_eq_mul,
    ← mul_assoc, map_inv ωπ, map_pow ωπ, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
    mul_inv_cancel₀ (pow_ne_zero _ (ωπ a).ne_zero), one_mul]

/-- The second dual function of the translated model is `ω_σ(a)^n` times the left
translate by `d_a` of the second dual function of the original model. -/
theorem secondDual_modelMap_characterChangeInverseFunctional
    (hσ : Classification.HasGLCentralCharacter F (n + 1) σ ωσ) (u : W)
    (h : Langlands.GeneralLinear (n + 1) F) :
    (secondDualFunction (ψ.scale a) n
        (modelMap σ (characterChangeInverseFunctional ψ σ a ℓ') u).val).val h =
      ((ωσ a : ℂˣ) : ℂ) ^ n *
        (characterChangeInverseFunction (ψ.scale (-1)) n a
          (secondDualFunction ψ n (modelMap σ ℓ' u).val)).val h := by
  rw [secondDualFunction_apply]
  change ℓ'.val (σ (characterChangeElement a n)
      (σ (weylLong (n + 1) F * inverseTranspose (n + 1) F h) u)) =
    _ * ℓ'.val (σ (weylLong (n + 1) F * inverseTranspose (n + 1) F
      (characterChangeElement a n * h)) u)
  have hm : weylLong (n + 1) F * inverseTranspose (n + 1) F (characterChangeElement a n * h) =
      (Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) (a ^ n))⁻¹ *
        (characterChangeElement a n * (weylLong (n + 1) F * inverseTranspose (n + 1) F h)) := by
    rw [map_mul (inverseTranspose (n + 1) F), inverseTranspose_characterChangeElement,
      ← mul_assoc, weylLong_mul_characterChangeElement_inv]
    simp only [mul_assoc]
  rw [hm, map_mul σ (Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) (a ^ n))⁻¹,
    Module.End.mul_apply, ← map_inv (Matrix.GeneralLinearGroup.scalar (Fin (n + 1))), hσ,
    map_smul, smul_eq_mul, map_mul σ (characterChangeElement a n), Module.End.mul_apply,
    ← mul_assoc, map_inv ωσ, map_pow ωσ, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
    mul_inv_cancel₀ (pow_ne_zero _ (ωσ a).ne_zero), one_mul]

end ModelFunctions

end Langlands.RankinSelberg
