import Langlands.Global.RankinSelberg.RealOppositeCompactChart
import Langlands.Global.RankinSelberg.RealOppositeGramBound
import Langlands.Global.RankinSelberg.RealPrincipalSeriesHeight
import Langlands.Global.RankinSelberg.RealMatrixConvergence
import Langlands.Representation.Archimedean.RealGramFunction
import Langlands.Representation.Archimedean.RealStrictCharacterLanglandsQuotient
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Compact-finite sections with arbitrary moments on the real opposite cell

Multiplying the polynomial of a Gram expression by a power of the product of the squared
bottom-right minors keeps the sign parity, hence the principal-series law. On the opposite cell
this multiplies the section by the corresponding inverse power of the product of the tail Gram
determinants, which gives arbitrary polynomial moments.
-/

noncomputable section

open MeasureTheory
open scoped Classical ContDiff Manifold Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealOppositeMoment

open Langlands.Archimedean (realPositionCharacter principalSeries principalSeriesCharacter
  unitaryCompact matrixModel)
open Langlands.Archimedean.GramFormula (padded det_padded diagonalTail gram gram_mul signReal
  signUnit shiftedExponent realPositionExponent complexify isUpperTriangular_diagonal_mul
  padded_apply_of_le padded_apply_of_lt)
open Langlands.Archimedean.RealGramFunction (gramFunction gramFunction_eq_extension HasSignParity
  gramFunction_mem_kFiniteFunctions orthogonalEval gramFunction_one)
open Langlands.Archimedean.PrincipalSeriesExtension (extension signedOrthogonalPart signedOrthogonal
  signedOrthogonal_mul)
open Langlands.LocalFactor.Archimedean (RealBlock RealCharacterData)
open Langlands.GeneralLinear (UpperEntryPair upperEntryCoordinates upperEntryCoordinates_apply
  inverseTranspose continuous_inverseTranspose)
open RealModulusOpenCell (realEntryLebesgue groupTranspose groupTranspose_val)
open RealOppositeGramBound (oppositeGramProduct one_le_oppositeGramProduct one_le_gram_transpose
  realOppositeGramBound)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "N" => fun n => Langlands.GeneralLinear.upperUnipotent n ℝ
local notation "Mat" => fun n => Matrix (Fin n) (Fin n) ℝ
local notation "Std" => Automorphic.realStandardKFinite

local instance realOppositeMomentMeasurable (n : ℕ) : MeasurableSpace (N n) := borel _
local instance realOppositeMomentBorel (n : ℕ) : BorelSpace (N n) := ⟨rfl⟩

variable {n : ℕ}

/-! ## Padded minors -/

private theorem padded_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (k : ℕ)
    (Y : Matrix (Fin n) (Fin n) R) : (padded k Y).map f = padded k (Y.map f) := by
  ext p q
  simp only [padded, Matrix.map_apply, Matrix.of_apply]
  split_ifs
  · rfl
  · rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp

/-- Padding a product with an upper triangular left factor is the product of the paddings. -/
theorem padded_mul_of_upper {R : Type*} [CommRing R] {b : Matrix (Fin n) (Fin n) R}
    (hb : b.IsUpperTriangular) (κ : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    padded k (b * κ) = padded k b * padded k κ := by
  ext p q
  rw [Matrix.mul_apply]
  by_cases hp : k ≤ (p : ℕ)
  · rw [Finset.sum_congr rfl fun r _ => by rw [padded_apply_of_le hb hp r]]
    by_cases hq : k ≤ (q : ℕ)
    · simp only [padded, Matrix.of_apply, if_pos (And.intro hp hq), Matrix.mul_apply]
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases hr : k ≤ (r : ℕ)
      · rw [if_pos (And.intro hr hq)]
      · rw [if_neg (fun h => hr h.1), Matrix.one_apply_ne (show r ≠ q from fun h => hr (h ▸ hq)),
          mul_zero,
          hb (show r < p from by rw [Fin.lt_def]; omega), zero_mul]
    · simp only [padded, Matrix.of_apply, if_neg (fun h : k ≤ (p : ℕ) ∧ k ≤ (q : ℕ) => hq h.2)]
      rw [Matrix.one_apply_ne (show p ≠ q from fun h => hq (h ▸ hp))]
      symm
      refine Finset.sum_eq_zero fun r _ => ?_
      by_cases hr : k ≤ (r : ℕ)
      · rw [if_neg (fun h => hq h.2), Matrix.one_apply_ne (show r ≠ q from fun h => hq (h ▸ hr)),
          mul_zero]
      · rw [hb (show r < p from by rw [Fin.lt_def]; omega), zero_mul]
  · rw [Finset.sum_congr rfl fun r _ => by rw [padded_apply_of_lt b (by omega : (p : ℕ) < k) r]]
    simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
    simp only [padded, Matrix.of_apply, if_neg (fun h : k ≤ (p : ℕ) ∧ k ≤ (q : ℕ) => hp h.1)]

private theorem det_padded_lower {L : Matrix (Fin n) (Fin n) ℝ} (hL : L.IsLowerTriangular)
    (hL1 : ∀ p, L p p = 1) (k : ℕ) : (padded k L).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · refine Finset.prod_eq_one fun p _ => ?_
    simp only [padded, Matrix.of_apply]
    split_ifs
    · exact hL1 p
    · exact Matrix.one_apply_eq p
  · intro p q hpq
    have hpq' : p < q := hpq
    simp only [padded, Matrix.of_apply]
    split_ifs
    · exact hL hpq
    · exact Matrix.one_apply_ne (ne_of_lt hpq')

/-! ## The moment polynomial -/

/-- The matrix of the coordinate variables. -/
private def varMatrix (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) ℂ) :=
  Matrix.of fun i j => MvPolynomial.X (i, j)

/-- The bottom-right minor on the rows and columns `≥ k`, as a polynomial. -/
def minorPoly (n k : ℕ) : MvPolynomial (Fin n × Fin n) ℂ := (padded k (varMatrix n)).det

private theorem eval_minorPoly (k : ℕ) (Y : Fin n × Fin n → ℂ) :
    MvPolynomial.eval Y (minorPoly n k) = (padded k (Matrix.of fun i j => Y (i, j))).det := by
  rw [minorPoly, RingHom.map_det, RingHom.mapMatrix_apply, padded_map]
  congr 2
  ext i j
  simp [varMatrix]

/-- The product of the squares of all bottom-right minors. -/
def momentPoly (n : ℕ) : MvPolynomial (Fin n × Fin n) ℂ := ∏ k : Fin n, minorPoly n k.val ^ 2

private theorem eval_momentPoly (Y : Fin n × Fin n → ℂ) :
    MvPolynomial.eval Y (momentPoly n) =
      ∏ k : Fin n, (padded k.val (Matrix.of fun i j => Y (i, j))).det ^ 2 := by
  simp only [momentPoly, map_prod, map_pow, eval_minorPoly]

private theorem eval_momentPoly_sign (a : Fin n → ℝˣ) (Y : Fin n × Fin n → ℂ) :
    MvPolynomial.eval (fun ij => ((signReal (a ij.1) : ℝ) : ℂ) * Y ij) (momentPoly n) =
      MvPolynomial.eval Y (momentPoly n) := by
  rw [eval_momentPoly, eval_momentPoly]
  refine Finset.prod_congr rfl fun k _ => ?_
  let σ : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun i => ((signReal (a i) : ℝ) : ℂ)
  have hσ : σ.IsUpperTriangular := Matrix.blockTriangular_diagonal _
  have hY : (Matrix.of fun i j => ((signReal (a (i, j).1) : ℝ) : ℂ) * Y (i, j)) =
      σ * Matrix.of fun i j => Y (i, j) := by
    ext i j
    simp [σ, Matrix.diagonal_mul]
  rw [hY, padded_mul_of_upper hσ, Matrix.det_mul, mul_pow, det_padded hσ]
  have h1 : diagonalTail k.val σ ^ 2 = 1 := by
    unfold diagonalTail
    rw [← Finset.prod_pow]
    refine Finset.prod_eq_one fun l _ => ?_
    split_ifs
    · simp only [σ, Matrix.diagonal_apply_eq]
      have : signReal (a l) ^ 2 = 1 := by unfold signReal; split_ifs <;> norm_num
      exact_mod_cast this
    · exact one_pow 2
  rw [h1, one_mul]

/-- The diagonal polynomial with the sign exponents of the characters. -/
def signPoly (ds : List RealBlock) (n : ℕ) : MvPolynomial (Fin n × Fin n) ℂ :=
  ∏ l : Fin n, MvPolynomial.X (l, l) ^
    (Classical.choose (Langlands.Archimedean.RealStrictCharacterLanglandsQuotient.exists_signs ds) l)

private theorem character_signUnit (ds : List RealBlock) (l : ℕ) (x : ℝˣ) :
    realPositionCharacter ds l (signUnit x) =
      ((signReal (x : ℝ) : ℝ) : ℂ) ^
        (Classical.choose (Langlands.Archimedean.RealStrictCharacterLanglandsQuotient.exists_signs ds) l) := by
  have hp := Classical.choose_spec
    (Langlands.Archimedean.RealStrictCharacterLanglandsQuotient.exists_signs ds) l
  have hone := (Langlands.Archimedean.RealStrictCharacterLanglandsQuotient.isSignedPower ds).one l
  unfold signUnit signReal
  split_ifs
  · simp [hone]
  · rw [hp]; push_cast; rfl

theorem signPoly_parity (ds : List RealBlock) :
    HasSignParity (realPositionCharacter ds) (signPoly ds n) := by
  intro a Y
  simp only [signPoly, map_prod, map_pow, MvPolynomial.eval_X, mul_pow,
    Finset.prod_mul_distrib, character_signUnit]

theorem momentPoly_parity (ds : List RealBlock) (m : ℕ) :
    HasSignParity (realPositionCharacter ds) (signPoly ds n * momentPoly n ^ m) := by
  intro a Y
  rw [map_mul, map_mul, map_pow, map_pow, signPoly_parity ds a Y, eval_momentPoly_sign, mul_assoc]

/-! ## The moment sections -/

/-- The Gram section of the sign polynomial times `m` powers of the moment polynomial. -/
def momentSection (n : ℕ) (ds : List RealBlock) (m : ℕ) : G n → ℂ :=
  gramFunction (shiftedExponent n (realPositionExponent ds)) (signPoly ds n * momentPoly n ^ m)

theorem momentSection_mem (cs : List RealCharacterData) (m : ℕ) :
    momentSection n (cs.map RealBlock.character) m ∈ Std n (cs.map RealBlock.character) := by
  have h := gramFunction_mem_kFiniteFunctions (n := n) (realPositionExponent _)
    (Langlands.Archimedean.RealStrictCharacterLanglandsQuotient.isSignedPower
      (cs.map RealBlock.character)).eq (momentPoly_parity (cs.map RealBlock.character) m)
  refine ⟨⟨h.1, fun p d hd => ?_⟩, h.2⟩
  rw [Langlands.Archimedean.RealPrincipalSeriesDuality.realInducedBlockAt_map_character] at hd
  exact absurd hd (by simp)

@[simp] theorem momentSection_one (n : ℕ) (ds : List RealBlock) (m : ℕ) :
    momentSection n ds m 1 = 1 := by
  rw [momentSection, gramFunction_one, map_mul, map_pow, eval_momentPoly]
  have h1 : (Matrix.of fun i j : Fin n =>
      ((((1 : Matrix (Fin n) (Fin n) ℝ) (i, j).1 (i, j).2 : ℝ) : ℂ))) =
      (1 : Matrix (Fin n) (Fin n) ℂ) := by
    ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have hpad (k : ℕ) : (padded k (1 : Matrix (Fin n) (Fin n) ℂ)).det = 1 := by
    rw [det_padded Matrix.blockTriangular_one]; simp [diagonalTail]
  have hsign : MvPolynomial.eval (fun ij : Fin n × Fin n =>
      (((1 : Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2 : ℝ) : ℂ)) (signPoly ds n) = 1 := by
    simp [signPoly, Matrix.one_apply]
  rw [hsign, one_mul]
  simp only [h1, hpad, one_pow, Finset.prod_const_one]

/-- On the transposed upper unipotent the moment polynomial of the signed orthogonal part is the
inverse of the product of tail Gram determinants. -/
theorem orthogonalEval_momentPoly_transpose (u : N n) :
    orthogonalEval (momentPoly n) (signedOrthogonalPart (groupTranspose u.val)) =
      (((oppositeGramProduct u)⁻¹ : ℝ) : ℂ) := by
  obtain ⟨a, v, κ, hκ, hx⟩ :=
    Langlands.Archimedean.exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact
      (groupTranspose u.val)
  set b : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun l => (a l : ℝ)) *
    ((v : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) with hbdef
  have hb : b.IsUpperTriangular := isUpperTriangular_diagonal_mul a v
  have hbd : ∀ l, b l l = a l := fun l => by
    rw [hbdef, Matrix.diagonal_mul, v.property.2 l, mul_one]
  have hd : ∀ l, b l l ≠ 0 := fun l => (hbd l).symm ▸ (a l).ne_zero
  have hκ' : (κ : Matrix (Fin n) (Fin n) ℝ) * (κ : Matrix (Fin n) (Fin n) ℝ)ᵀ = 1 :=
    Langlands.Archimedean.GramFormula.mul_transpose_eq_one_of_mem hκ
  have hX : (groupTranspose u.val).val = b * (κ : Matrix (Fin n) (Fin n) ℝ) := by
    rw [hx]; rfl
  have hhat : ((signedOrthogonalPart (groupTranspose u.val) :
      Matrix.unitaryGroup (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) =
      Matrix.diagonal (fun i => signReal (b i i)) * (κ : Matrix (Fin n) (Fin n) ℝ) := by
    change signedOrthogonal (groupTranspose u.val).val = _
    rw [hX, signedOrthogonal_mul hb hd hκ']
  have hL : (groupTranspose u.val).val.IsLowerTriangular := by
    rw [groupTranspose_val]
    exact fun _ _ h => Langlands.GeneralLinear.UpperUnipotent.entry_eq_zero u h
  have hL1 : ∀ p, (groupTranspose u.val).val p p = 1 := fun p => by
    rw [groupTranspose_val]
    exact Langlands.GeneralLinear.UpperUnipotent.entry_diag u p
  have hminor (k : ℕ) : (padded k (κ : Matrix (Fin n) (Fin n) ℝ)).det ^ 2 =
      (gram k (groupTranspose u.val).val)⁻¹ := by
    have h1 := det_padded_lower hL hL1 k
    rw [hX, padded_mul_of_upper hb, Matrix.det_mul, det_padded hb] at h1
    rw [hX, gram_mul hb hκ', eq_inv_of_mul_eq_one_right h1, inv_pow]
  have hsign (k : ℕ) : (padded k (Matrix.diagonal (fun i => signReal (b i i)) *
      (κ : Matrix (Fin n) (Fin n) ℝ))).det ^ 2 = (padded k (κ : Matrix (Fin n) (Fin n) ℝ)).det ^ 2 := by
    rw [padded_mul_of_upper (Matrix.blockTriangular_diagonal _), Matrix.det_mul, mul_pow,
      det_padded (Matrix.blockTriangular_diagonal _)]
    have h1 : diagonalTail k (Matrix.diagonal (fun i => signReal (b i i))) ^ 2 = 1 := by
      unfold diagonalTail
      rw [← Finset.prod_pow]
      refine Finset.prod_eq_one fun l _ => ?_
      split_ifs
      · simp only [Matrix.diagonal_apply_eq]
        unfold signReal; split_ifs <;> norm_num
      · exact one_pow 2
    rw [h1, one_mul]
  rw [orthogonalEval, eval_momentPoly, oppositeGramProduct, Complex.ofReal_inv, Complex.ofReal_prod,
    ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hmap : (Matrix.of fun i j => ((((signedOrthogonalPart (groupTranspose u.val) :
      Matrix.unitaryGroup (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) (i, j).1 (i, j).2 : ℝ) : ℂ)) =
      (((signedOrthogonalPart (groupTranspose u.val) : Matrix.unitaryGroup (Fin n) ℝ) :
        Matrix (Fin n) (Fin n) ℝ)).map (Complex.ofRealHom) := by
    ext i j; rfl
  rw [hmap, ← padded_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← map_pow, hhat, hsign,
    hminor, groupTranspose_val]
  simp

/-- Increasing the moment exponent by `j` multiplies the opposite-cell restriction by the
`j`-th power of the inverse Gram product. -/
theorem momentSection_add_opposite (ds : List RealBlock) (m j : ℕ) (u : N n) :
    momentSection n ds (m + j) (groupTranspose u.val) =
      momentSection n ds m (groupTranspose u.val) * (((oppositeGramProduct u)⁻¹ : ℝ) : ℂ) ^ j := by
  simp only [momentSection, gramFunction_eq_extension, extension]
  rw [← orthogonalEval_momentPoly_transpose u]
  simp only [orthogonalEval, map_mul, map_pow, pow_add, mul_assoc]

open scoped Matrix.Norms.Operator in
theorem continuous_momentSection (cs : List RealCharacterData) (m : ℕ) :
    Continuous (momentSection n (cs.map RealBlock.character) m) :=
  (momentSection_mem cs m).1.1.1.continuous

open scoped Matrix.Norms.Operator in
theorem contMDiff_momentSection (ds : List RealBlock) (m : ℕ) :
    ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ (momentSection n ds m) :=
  Langlands.Archimedean.RealGramFunction.contMDiff_gramFunction _ _

open scoped Matrix.Norms.Operator in
theorem continuous_momentSection' (ds : List RealBlock) (m : ℕ) :
    Continuous (momentSection n ds m) :=
  (contMDiff_momentSection ds m).continuous

theorem momentSection_mem_principalSeries (ds : List RealBlock) (m : ℕ) :
    momentSection n ds m ∈ principalSeries ℝ n (realPositionCharacter ds) :=
  Langlands.Archimedean.RealGramFunction.gramFunction_mem_principalSeries (realPositionExponent ds)
    (Langlands.Archimedean.RealStrictCharacterLanglandsQuotient.isSignedPower ds).eq
    (momentPoly_parity ds m)

/-! ## Moments -/

section Moments

open scoped Matrix.Norms.Elementwise

/-- In exact entry coordinates the entrywise distance of an upper unipotent from one is the
coordinate supremum norm. -/
theorem norm_upperEntries (u : N n) :
    ‖upperEntryCoordinates n u‖ = ‖u.val.val - 1‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro ij
    have h := Matrix.norm_entry_le_entrywise_sup_norm (u.val.val - 1) (i := ij.1.1) (j := ij.1.2)
    simpa only [upperEntryCoordinates_apply, Matrix.sub_apply,
      Matrix.one_apply_ne ij.2.ne, sub_zero] using h
  · apply (Matrix.norm_le_iff (norm_nonneg _)).mpr
    intro i j
    rw [Matrix.sub_apply]
    rcases lt_trichotomy i j with hij | rfl | hji
    · rw [Matrix.one_apply_ne hij.ne, sub_zero]
      simpa only [upperEntryCoordinates_apply] using
        norm_le_pi_norm (upperEntryCoordinates n u) ⟨(i, j), hij⟩
    · rw [Langlands.GeneralLinear.UpperUnipotent.entry_diag, Matrix.one_apply_eq, sub_self,
        norm_zero]
      positivity
    · rw [Langlands.GeneralLinear.UpperUnipotent.entry_eq_zero u hji, Matrix.one_apply_ne hji.ne',
        sub_zero, norm_zero]
      positivity

theorem measurePreserving_upperEntryInverse (n : ℕ) :
    MeasurePreserving (upperEntryCoordinates (K := ℝ) n).symm volume (realEntryLebesgue n) := by
  refine ⟨(upperEntryCoordinates (K := ℝ) n).symm.measurable, ?_⟩
  rw [volume_pi]
  rfl

private theorem integrable_inverse_displacement_pow (n p : ℕ)
    (hp : Module.finrank ℝ (UpperEntryPair n → ℝ) < 2 * p) :
    Integrable (fun u : N n => ((1 + ‖u.val.val - 1‖ ^ 2) ^ p)⁻¹) (realEntryLebesgue n) := by
  let e := upperEntryCoordinates (K := ℝ) n
  apply ((measurePreserving_upperEntryInverse n).integrable_comp_emb
    e.symm.toMeasurableEquiv.measurableEmbedding).mp
  have hi : Integrable (fun X : UpperEntryPair n → ℝ => (1 + ‖X‖ ^ 2) ^ (-(2 * (p : ℝ)) / 2))
      volume :=
    integrable_rpow_neg_one_add_norm_sq (by exact_mod_cast hp)
  refine hi.congr (ae_of_all _ fun X => ?_)
  change (1 + ‖X‖ ^ 2) ^ (-(2 * (p : ℝ)) / 2) = ((1 + ‖(e.symm X).val.val - 1‖ ^ 2) ^ p)⁻¹
  rw [← norm_upperEntries (e.symm X),
    show upperEntryCoordinates n (e.symm X) = X from e.apply_symm_apply X,
    show -(2 * (p : ℝ)) / 2 = -(p : ℝ) by ring, Real.rpow_neg (by positivity), Real.rpow_natCast]

private theorem norm_entry_le (u : N n) (i j : Fin n) :
    ‖u.val.val j i‖ ≤ 1 + ‖u.val.val - 1‖ := by
  have h := Matrix.norm_entry_le_entrywise_sup_norm (u.val.val - 1) (i := j) (j := i)
  have h1 : ‖(1 : Matrix (Fin n) (Fin n) ℝ) j i‖ ≤ 1 := by
    rw [Matrix.one_apply]; split_ifs <;> simp
  calc
    ‖u.val.val j i‖ = ‖(u.val.val - 1) j i + (1 : Matrix (Fin n) (Fin n) ℝ) j i‖ := by
      rw [Matrix.sub_apply, sub_add_cancel]
    _ ≤ ‖(u.val.val - 1) j i‖ + ‖(1 : Matrix (Fin n) (Fin n) ℝ) j i‖ := norm_add_le _ _
    _ ≤ _ := by linarith

end Moments

section Height

open scoped Matrix.Norms.Operator

private theorem opNorm_le_sum (A : Matrix (Fin n) (Fin n) ℝ) : ‖A‖ ≤ ∑ i, ∑ j, ‖A i j‖ := by
  change (‖A‖₊ : ℝ) ≤ _
  rw [Matrix.linfty_opNNNorm_def]
  have h : (Finset.univ.sup fun i => ∑ j, ‖A i j‖₊) ≤ ∑ i, ∑ j, ‖A i j‖₊ := by
    refine Finset.sup_le fun i _ => ?_
    exact Finset.single_le_sum (f := fun i => ∑ j, ‖A i j‖₊) (fun _ _ => bot_le)
      (Finset.mem_univ i)
  have h' := NNReal.coe_le_coe.mpr h
  simpa only [NNReal.coe_sum, coe_nnnorm] using h'

private theorem det_groupTranspose_unipotent (u : N n) : (groupTranspose u.val).val.det = 1 := by
  rw [groupTranspose_val, Matrix.det_transpose]
  exact Langlands.Archimedean.MaximalParabolicIntegration.det_upperUnipotent _

/-- The real matrix height of a transposed upper unipotent is polynomial in its entrywise
distance from one. -/
theorem realMatrixHeight_transpose_le (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : N (r + 1)) (t : ℝ),
      (∀ i j : Fin (r + 1), ‖u.val.val j i‖ ≤ 1 + t) → 0 ≤ t →
      realMatrixHeight (groupTranspose u.val) ≤ C * (1 + t) ^ (2 * (r + 1 + 1)) := by
  refine ⟨2 * ((r : ℝ) + 1) ^ 2 * ((r + 1).factorial : ℝ) ^ 2 *
    (1 + ((r : ℝ) + 1) ^ 2) ^ (2 * (r + 1 + 1)), by positivity, fun u t he ht => ?_⟩
  have hH := Langlands.GodementJacquet.realMatrixHeight_mul_absDet_sq_bound (r := r)
    (groupTranspose u.val)
  rw [det_groupTranspose_unipotent, abs_one, one_pow, mul_one] at hH
  have hnorm : ‖(groupTranspose u.val).val‖ ≤ ((r : ℝ) + 1) ^ 2 * (1 + t) := by
    refine (opNorm_le_sum _).trans ?_
    rw [groupTranspose_val]
    calc
      (∑ i : Fin (r + 1), ∑ j : Fin (r + 1), ‖u.val.valᵀ i j‖) ≤
          ∑ _i : Fin (r + 1), ∑ _j : Fin (r + 1), (1 + t) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => he i j
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring
  push_cast at hH
  calc
    _ ≤ 2 * ((r : ℝ) + 1) ^ 2 * ((r + 1).factorial : ℝ) ^ 2 *
        (1 + ‖(groupTranspose u.val).val‖) ^ (2 * (r + 1 + 1)) := hH
    _ ≤ 2 * ((r : ℝ) + 1) ^ 2 * ((r + 1).factorial : ℝ) ^ 2 *
        ((1 + ((r : ℝ) + 1) ^ 2) * (1 + t)) ^ (2 * (r + 1 + 1)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [sq_nonneg ((r : ℝ) + 1)]
    _ = _ := by rw [mul_pow]; ring

end Height

open scoped Matrix.Norms.Elementwise

/-- At fixed inducing data and any polynomial order, all sufficiently large moment exponents
give an absolutely integrable weighted opposite-cell restriction under entry Lebesgue measure. -/
def RealOppositeMomentStatement : Prop :=
  ∀ (r : ℕ) (ds : List RealBlock) (L : ℕ), ∃ m₀ : ℕ, ∀ m ≥ m₀,
    Integrable (fun u : N (r + 1) =>
        (1 + ‖u.val.val - 1‖) ^ L • momentSection (r + 1) ds m (groupTranspose u.val))
      (realEntryLebesgue (r + 1))

theorem realOppositeMoment : RealOppositeMomentStatement := by
  intro r ds L
  let n := r + 1
  let p : ℕ := Module.finrank ℝ (UpperEntryPair n → ℝ) + 1
  have hp : Module.finrank ℝ (UpperEntryPair n → ℝ) < 2 * p := by dsimp [p]; omega
  obtain ⟨A, N₀, hA, hHeight⟩ :=
    RealPrincipalSeries.realPrincipalSeriesHeight n (Nat.succ_pos r) ds
  obtain ⟨Cb, hCb⟩ := Langlands.Archimedean.PartialJacquet.exists_bound_unitaryCompact
    (continuous_momentSection' (n := n) ds 0)
  obtain ⟨Ch, hCh, hH⟩ := realMatrixHeight_transpose_le r
  let E : ℕ := 2 * (n + 1) * N₀
  refine ⟨E + L + p, fun m hm => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, m = 0 + j := ⟨m, (zero_add m).symm⟩
  have hT : Continuous (fun u : N n => groupTranspose u.val) :=
    ((continuous_inverseTranspose n ℝ).comp continuous_inv).comp continuous_subtype_val
  have hnorm : Continuous (fun u : N n => ‖u.val.val - 1‖) :=
    (((Units.continuous_val (M := Matrix (Fin n) (Fin n) ℝ)).comp continuous_subtype_val).sub
      continuous_const).norm
  have hcont : Continuous (fun u : N n =>
      (1 + ‖u.val.val - 1‖) ^ L • momentSection n ds (0 + j) (groupTranspose u.val)) :=
    ((continuous_const.add hnorm).pow L).smul
      ((continuous_momentSection' (n := n) ds (0 + j)).comp hT)
  let K₀ : ℝ := A * max Cb 0 * Ch ^ N₀ * 2 ^ (2 * (n + 1) * N₀) * 2 ^ L
  have hK₀ : 0 ≤ K₀ := by positivity
  refine ((integrable_inverse_displacement_pow n p hp).const_mul K₀).mono'
    hcont.aestronglyMeasurable (ae_of_all _ fun u => ?_)
  let R := oppositeGramProduct u
  let t := ‖u.val.val - 1‖
  have hR1 : 1 ≤ R := one_le_oppositeGramProduct u
  have hR : 0 < R := zero_lt_one.trans_le hR1
  have ht : 0 ≤ t := norm_nonneg _
  have hGram : 1 + t ^ 2 ≤ R := realOppositeGramBound n u
  have htR : 1 + t ≤ 2 * R := by nlinarith [sq_nonneg (t - 1)]
  have hbase : ‖momentSection n ds 0 (groupTranspose u.val)‖ ≤ K₀ / 2 ^ L * R ^ E := by
    have h0 := hHeight (momentSection n ds 0) (momentSection_mem_principalSeries ds 0) (max Cb 0)
      (fun k hk => (hCb k hk).trans (le_max_left _ _)) (groupTranspose u.val)
    have hHt := hH u t (fun i j => norm_entry_le u i j) ht
    have hHnn : 0 ≤ realMatrixHeight (groupTranspose u.val) := RealPlaceRestriction.realMatrixHeight_nonneg _
    calc
      _ ≤ A * max Cb 0 * realMatrixHeight (groupTranspose u.val) ^ N₀ := h0
      _ ≤ A * max Cb 0 * (Ch * (1 + t) ^ (2 * (r + 1 + 1))) ^ N₀ :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hHnn hHt _) (by positivity)
      _ ≤ A * max Cb 0 * (Ch * (2 * R) ^ (2 * (n + 1))) ^ N₀ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply pow_le_pow_left₀ (by positivity)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) htR _) hCh
      _ = K₀ / 2 ^ L * R ^ E := by
        simp only [K₀, E, mul_pow, ← pow_mul]
        field_simp
  have hRinv : ‖(((oppositeGramProduct u)⁻¹ : ℝ) : ℂ) ^ j‖ = (R ^ j)⁻¹ := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hR, inv_pow]
  have hj : E + L + p ≤ j := by simpa using hm
  change ‖(1 + t) ^ L • momentSection n ds (0 + j) (groupTranspose u.val)‖ ≤
    K₀ * ((1 + t ^ 2) ^ p)⁻¹
  rw [momentSection_add_opposite, norm_smul, norm_mul, hRinv,
    Real.norm_of_nonneg (by positivity)]
  have hpowL : (1 + t) ^ L ≤ 2 ^ L * R ^ L := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) htR L
  have hRj : R ^ (E + L + p) ≤ R ^ j := pow_le_pow_right₀ hR1 hj
  calc
    _ ≤ (2 ^ L * R ^ L) * ((K₀ / 2 ^ L * R ^ E) * (R ^ j)⁻¹) :=
      mul_le_mul hpowL (mul_le_mul_of_nonneg_right hbase (by positivity)) (by positivity)
        (by positivity)
    _ ≤ (2 ^ L * R ^ L) * ((K₀ / 2 ^ L * R ^ E) * (R ^ (E + L + p))⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact inv_anti₀ (by positivity) hRj
    _ = K₀ * (R ^ p)⁻¹ := by
      rw [pow_add, pow_add]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hGram p)) hK₀

end Langlands.Global.RankinSelbergGlobal.RealOppositeMoment
