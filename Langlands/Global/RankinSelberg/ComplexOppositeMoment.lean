import Langlands.Global.RankinSelberg.ComplexModulusOpenCell
import Langlands.Global.RankinSelberg.ComplexOppositeGramBound
import Langlands.Automorphic.ArchimedeanPlaceParameter
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Compact-finite sections with arbitrary moments on the complex opposite cell

The minor powers of the standard nonzero section can both be increased by `m`
if its Gram exponent is decreased by `m`. These changes keep the Borel
character and give arbitrary polynomial moments on the opposite cell.
-/

noncomputable section

open MeasureTheory
open scoped Classical ContDiff Manifold Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexOppositeMoment

open GeneralLinear (UpperEntryPair upperEntryCoordinates upperEntryCoordinates_apply upperUnipotent
  inverseTranspose continuous_inverseTranspose)
open Langlands.Archimedean (complexPositionCharacter principalSeriesCharacter unitaryCompact matrixModel
  contMDiff_of_contDiffOn minorFactor nzWeight nzExponent nzFactor nzFunction lowGram
  contDiffOn_minorFactor minorFn_mem expFn_mem kFiniteSubalgebra polyChar unitChar
  unitChar_zero_zero polyChar_eq_unitChar minorFactor_mul_of_isUpperTriangular
  nzFunction_mul_of_isUpperTriangular principalSeriesCharacter_eq lowMinor lowMinor_one lowGram_one)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open ComplexModulusOpenCell (complexEntryLebesgue groupTranspose groupTranspose_val)
open ComplexOppositeGramBound (lowMinor_transpose_unipotent one_le_lowGram_transpose
  oppositeGramProduct one_le_oppositeGramProduct complexOppositeGramBound)

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "N" => fun n => upperUnipotent n ℂ
local notation "Mat" => fun n => Matrix (Fin n) (Fin n) ℂ
local notation "Std" => Automorphic.complexStandardKFinite

local instance oppositeMomentMeasurable (n : ℕ) : MeasurableSpace (N n) := borel _
local instance oppositeMomentBorel (n : ℕ) : BorelSpace (N n) := ⟨rfl⟩

private def gramExponent (n : ℕ) (ds : List ComplexCharacterData) (k : ℕ) : ℂ :=
  nzExponent n ds k - (((nzWeight ds k).toNat : ℂ) + ((-nzWeight ds k).toNat : ℂ)) / 2

private def momentFactor (n : ℕ) (ds : List ComplexCharacterData) (m k : ℕ) (A : Mat n) : ℂ :=
  minorFactor k ((nzWeight ds k).toNat + m) ((-nzWeight ds k).toNat + m)
    (gramExponent n ds k - (m : ℂ)) A

/-- The standard minor section with `m` additional powers of the bottom-right minors and their
conjugates, cancelled by `m` inverse powers of the corresponding Gram determinants. -/
def momentSection (n : ℕ) (ds : List ComplexCharacterData) (m : ℕ) (g : G n) : ℂ :=
  ∏ k : Fin n, momentFactor n ds m k.val g.val

private theorem momentFactor_eq (n : ℕ) (ds : List ComplexCharacterData) (m k : ℕ) (A : Mat n) :
    momentFactor n ds m k A = nzFactor n ds k A * minorFactor k m m (-(m : ℂ)) A := by
  simp only [momentFactor, nzFactor, gramExponent, minorFactor, pow_add, sub_mul, neg_mul,
    Complex.exp_sub, Complex.exp_neg, div_eq_mul_inv]
  ring

private theorem momentSection_eq {n : ℕ} (ds : List ComplexCharacterData) (m : ℕ) (g : G n) :
    momentSection n ds m g = nzFunction n ds g.val *
      ∏ k : Fin n, minorFactor k.val m m (-(m : ℂ)) g.val := by
  simp only [momentSection, momentFactor_eq, Finset.prod_mul_distrib, nzFunction]

private theorem polyChar_neutral (m : ℕ) {z : ℂ} (hz : z ≠ 0) : polyChar m m (-(m : ℂ)) z = 1 := by
  have h : ((m : ℂ) + m) / 2 + -(m : ℂ) = 0 := by ring
  rw [polyChar_eq_unitChar _ _ _ hz, sub_self, h, unitChar_zero_zero]

open scoped Matrix.Norms.Operator in
/-- All shifts have the same principal-series covariance and finite unitary translate span. -/
theorem momentSection_mem (n : ℕ) (ds : List ComplexCharacterData) (m : ℕ) :
    momentSection n ds m ∈ Std n ds := by
  have hdiff : ContDiffOn ℝ ∞ (fun A : Mat n => ∏ k : Fin n, momentFactor n ds m k.val A)
      {A | IsUnit A} :=
    contDiffOn_prod fun k _ => contDiffOn_minorFactor k.val _ _ _
  have hs : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ (momentSection n ds m) :=
    contMDiff_of_contDiffOn hdiff (fun _ => rfl)
  refine ⟨⟨hs, fun a u g => ?_⟩, ?_⟩
  · let b : Mat n := Matrix.diagonal (fun i => (a i : ℂ)) * u.val.val
    have hb : b.IsUpperTriangular := (Matrix.blockTriangular_diagonal _).mul u.2.1
    have hd (i : Fin n) : b i i = a i := by
      change (Matrix.diagonal (fun j => (a j : ℂ)) * u.val.val) i i = a i
      rw [Matrix.diagonal_mul, u.2.2 i, mul_one]
    have hd0 : ∀ i, b i i ≠ 0 := fun i => (hd i).symm ▸ (a i).ne_zero
    have hbprod : (GeneralLinear.Iwasawa.diagonalUnits a * u.val * g : G n).val = b * g.val := rfl
    have hchar : (∏ i : Fin n, unitChar (Langlands.Archimedean.posWeight ds i)
        (Langlands.Archimedean.nzFullExponent n ds i) (b i i)) =
        principalSeriesCharacter ℂ n (complexPositionCharacter ds) a := by
      rw [principalSeriesCharacter_eq]
      exact Finset.prod_congr rfl fun i _ => congrArg _ (hd i)
    have hshift (k : Fin n) : minorFactor k.val m m (-(m : ℂ)) (b * g.val) =
        minorFactor k.val m m (-(m : ℂ)) g.val := by
      rw [minorFactor_mul_of_isUpperTriangular _ _ _ _ hb
        (Finset.prod_ne_zero_iff.mpr fun i _ => hd0 i.val) (Units.isUnit g),
        polyChar_neutral m (Finset.prod_ne_zero_iff.mpr fun i _ => hd0 i.val), one_mul]
    simp_rw [momentSection_eq, hbprod, nzFunction_mul_of_isUpperTriangular ds hb hd0 (Units.isUnit g),
      hchar, hshift, mul_assoc]
  · change momentSection n ds m ∈ kFiniteSubalgebra (unitaryCompact ℂ n)
    have he : momentSection n ds m = ∏ k : Fin n, fun g : G n => momentFactor n ds m k.val g.val := by
      funext g
      simp only [momentSection, Finset.prod_apply]
    rw [he]
    refine Subalgebra.prod_mem _ fun k _ => ?_
    exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _
      (Subalgebra.pow_mem _ (minorFn_mem (RingHom.id ℂ) k.val) _)
      (Subalgebra.pow_mem _ (minorFn_mem (starRingEnd ℂ) k.val) _)) (expFn_mem _ k.val)

@[simp] theorem momentSection_one (n : ℕ) (ds : List ComplexCharacterData) (m : ℕ) :
    momentSection n ds m 1 = 1 := by
  simp [momentSection, momentFactor, minorFactor, lowMinor_one, lowGram_one]

/-- Increasing the shift by `j` multiplies the opposite-cell restriction by the inverse Gram
product to the `j`-th power. -/
theorem momentSection_add_opposite {n : ℕ} (ds : List ComplexCharacterData) (m j : ℕ) (u : N n) :
    momentSection n ds (m + j) (groupTranspose u.val) =
      momentSection n ds m (groupTranspose u.val) * (((oppositeGramProduct u)⁻¹ : ℝ) : ℂ) ^ j := by
  have hfactor (a : ℕ) (k : Fin n) :
      minorFactor k.val a a (-(a : ℂ)) (groupTranspose u.val).val =
        ((((lowGram k.val u.val.valᵀ).re ^ a)⁻¹ : ℝ) : ℂ) := by
    simp only [groupTranspose_val, minorFactor, lowMinor_transpose_unipotent, map_one, one_pow, one_mul]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
      neg_mul, Real.exp_neg, Real.exp_nat_mul,
      Real.exp_log (zero_lt_one.trans_le (one_le_lowGram_transpose u k.val))]
  have hprod (a : ℕ) :
      (∏ k : Fin n, minorFactor k.val a a (-(a : ℂ)) (groupTranspose u.val).val) =
        ((((oppositeGramProduct u) ^ a)⁻¹ : ℝ) : ℂ) := by
    simp only [hfactor, ← Complex.ofReal_prod, Finset.prod_inv_distrib, Finset.prod_pow, oppositeGramProduct]
  simp only [momentSection_eq, hprod, pow_add, mul_inv, ← inv_pow, Complex.ofReal_mul,
    Complex.ofReal_pow, mul_assoc]

open scoped Matrix.Norms.Operator in
theorem continuous_momentSection (n : ℕ) (ds : List ComplexCharacterData) (m : ℕ) :
    Continuous (momentSection n ds m) :=
  (momentSection_mem n ds m).1.1.continuous

private theorem norm_momentSection_opposite {n : ℕ} (ds : List ComplexCharacterData) (m : ℕ)
    (u : N n) :
    ‖momentSection n ds m (groupTranspose u.val)‖ =
      ∏ k : Fin n, (lowGram k.val u.val.valᵀ).re ^ ((gramExponent n ds k.val).re - (m : ℝ)) := by
  simp only [momentSection, norm_prod, momentFactor, groupTranspose_val, minorFactor,
    lowMinor_transpose_unipotent, map_one, one_pow, one_mul, Complex.norm_exp, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.sub_re, Complex.natCast_re]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Real.rpow_def_of_pos (zero_lt_one.trans_le (one_le_lowGram_transpose u k.val)), mul_comm]

open scoped Matrix.Norms.Elementwise

/-- In exact entry coordinates the entrywise distance of an upper unipotent from one is the
coordinate supremum norm. -/
theorem norm_upperEntries {n : ℕ} (u : N n) :
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
    · rw [GeneralLinear.UpperUnipotent.entry_diag, Matrix.one_apply_eq, sub_self, norm_zero]
      positivity
    · rw [GeneralLinear.UpperUnipotent.entry_eq_zero u hji, Matrix.one_apply_ne hji.ne', sub_zero, norm_zero]
      positivity

theorem measurePreserving_upperEntryInverse (n : ℕ) :
    MeasurePreserving (upperEntryCoordinates (K := ℂ) n).symm volume (complexEntryLebesgue n) := by
  refine ⟨(upperEntryCoordinates (K := ℂ) n).symm.measurable, ?_⟩
  rw [volume_pi]
  rfl

private theorem integrable_inverse_displacement_pow (n p : ℕ)
    (hp : Module.finrank ℝ (UpperEntryPair n → ℂ) < 2 * p) :
    Integrable (fun u : N n => ((1 + ‖u.val.val - 1‖ ^ 2) ^ p)⁻¹) (complexEntryLebesgue n) := by
  let e := upperEntryCoordinates (K := ℂ) n
  apply ((measurePreserving_upperEntryInverse n).integrable_comp_emb
    e.symm.toMeasurableEquiv.measurableEmbedding).mp
  have hi : Integrable (fun X : UpperEntryPair n → ℂ => (1 + ‖X‖ ^ 2) ^ (-(2 * (p : ℝ)) / 2)) volume :=
    integrable_rpow_neg_one_add_norm_sq (by exact_mod_cast hp)
  refine hi.congr (ae_of_all _ fun X => ?_)
  change (1 + ‖X‖ ^ 2) ^ (-(2 * (p : ℝ)) / 2) = ((1 + ‖(e.symm X).val.val - 1‖ ^ 2) ^ p)⁻¹
  rw [← norm_upperEntries (e.symm X), show upperEntryCoordinates n (e.symm X) = X from e.apply_symm_apply X,
    show -(2 * (p : ℝ)) / 2 = -(p : ℝ) by ring, Real.rpow_neg (by positivity), Real.rpow_natCast]

private theorem norm_momentSection_le {n : ℕ} (ds : List ComplexCharacterData) (m q : ℕ)
    (hm : ∀ i : Fin n, (gramExponent n ds i.val).re - (m : ℝ) ≤ -(q : ℝ)) (u : N n) :
    ‖momentSection n ds m (groupTranspose u.val)‖ ≤ ((oppositeGramProduct u) ^ q)⁻¹ := by
  rw [norm_momentSection_opposite]
  calc
    _ ≤ ∏ i : Fin n, (((lowGram i.val u.val.valᵀ).re) ^ q)⁻¹ := by
      refine Finset.prod_le_prod₀ (fun i _ => Real.rpow_nonneg
        ((zero_le_one : (0 : ℝ) ≤ 1).trans (one_le_lowGram_transpose u i.val)) _) fun i _ => ?_
      have hx := one_le_lowGram_transpose u i.val
      simpa only [Real.rpow_neg ((zero_le_one : (0 : ℝ) ≤ 1).trans hx), Real.rpow_natCast] using
        Real.rpow_le_rpow_of_exponent_le hx (hm i)
    _ = _ := by rw [Finset.prod_inv_distrib, Finset.prod_pow, oppositeGramProduct]

/-- At fixed inducing data and any polynomial order, all sufficiently large minor shifts have
an absolutely integrable weighted opposite-cell restriction under exact entry Lebesgue measure. -/
def ComplexOppositeMomentStatement : Prop :=
  ∀ (n : ℕ) (ds : List ComplexCharacterData) (L : ℕ), ∃ m₀ : ℕ, ∀ m ≥ m₀,
    Integrable (fun u : N n => (1 + ‖u.val.val - 1‖) ^ L • momentSection n ds m (groupTranspose u.val))
      (complexEntryLebesgue n)

theorem complexOppositeMoment : ComplexOppositeMomentStatement := by
  intro n ds L
  let p : ℕ := Module.finrank ℝ (UpperEntryPair n → ℂ) + 1
  have hp : Module.finrank ℝ (UpperEntryPair n → ℂ) < 2 * p := by dsimp [p]; omega
  let S : ℝ := ∑ i : Fin n, |(gramExponent n ds i.val).re|
  obtain ⟨m₀, hm₀⟩ := exists_nat_gt (S + ((L + p : ℕ) : ℝ))
  refine ⟨m₀, fun m hm => ?_⟩
  have hm' : (m₀ : ℝ) ≤ m := by exact_mod_cast hm
  have hσ (i : Fin n) : (gramExponent n ds i.val).re - (m : ℝ) ≤ -((L + p : ℕ) : ℝ) := by
    have hs : |(gramExponent n ds i.val).re| ≤ S :=
      Finset.single_le_sum (fun k _ => abs_nonneg (gramExponent n ds k.val).re) (Finset.mem_univ i)
    linarith [le_abs_self (gramExponent n ds i.val).re]
  have hT : Continuous (fun u : N n => groupTranspose u.val) :=
    ((continuous_inverseTranspose n ℂ).comp continuous_inv).comp continuous_subtype_val
  have hnorm : Continuous (fun u : N n => ‖u.val.val - 1‖) :=
    (((Units.continuous_val (M := Mat n)).comp continuous_subtype_val).sub continuous_const).norm
  have hcont : Continuous (fun u : N n =>
      (1 + ‖u.val.val - 1‖) ^ L • momentSection n ds m (groupTranspose u.val)) :=
    ((continuous_const.add hnorm).pow L).smul ((continuous_momentSection n ds m).comp hT)
  refine ((integrable_inverse_displacement_pow n p hp).const_mul ((2 : ℝ) ^ L)).mono'
    hcont.aestronglyMeasurable (ae_of_all _ fun u => ?_)
  let R := oppositeGramProduct u
  let t := ‖u.val.val - 1‖
  have hR : 0 < R := zero_lt_one.trans_le (one_le_oppositeGramProduct u)
  have ht : 0 ≤ t := norm_nonneg _
  have hGram : 1 + t ^ 2 ≤ R := complexOppositeGramBound n u
  have htR : 1 + t ≤ 2 * R := by nlinarith [sq_nonneg (t - 1)]
  have hpow : (1 + t) ^ L ≤ (2 : ℝ) ^ L * R ^ L := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) htR L
  change ‖(1 + t) ^ L • momentSection n ds m (groupTranspose u.val)‖ ≤
    (2 : ℝ) ^ L * ((1 + t ^ 2) ^ p)⁻¹
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ ((2 : ℝ) ^ L * R ^ L) * (R ^ (L + p))⁻¹ :=
      mul_le_mul hpow (norm_momentSection_le ds m (L + p) hσ u) (norm_nonneg _) (by positivity)
    _ = (2 : ℝ) ^ L * (R ^ p)⁻¹ := by rw [pow_add]; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hGram p)) (by positivity)

end Langlands.Global.RankinSelbergGlobal.ComplexOppositeMoment
