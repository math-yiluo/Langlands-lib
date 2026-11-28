import Langlands.Global.RankinSelberg.RealLocalEqualUnfolding
import Langlands.Global.RankinSelberg.RealGodementSchwartzMajorant

/-! # Joint absolute convergence of the real unfolded equal-rank integral -/

noncomputable section

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean Langlands.Whittaker
open Langlands.QuotientIntegration
open Langlands.Global.RankinSelbergGlobal.RealIwasawa
open Langlands.Global.RankinSelbergGlobal.RealConvergenceAnalysis
open Langlands.RankinSelberg (LeftUnipotentQuotient lastRow lastRow_unipotent_mul unipotent_det)
open MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped Matrix.Norms.Operator SchwartzMap NNReal ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open ArchimedeanLocal
open Langlands.Archimedean (unitaryCompact)

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent (n + 1) ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (GeneralLinear.upperUnipotent (n + 1) ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

variable {t : ℕ}

local notation "m" => (t + 1)
local notation "n" => (t + 2)
local notation "G" => Langlands.GeneralLinear (t + 1) ℝ
local notation "H" => Langlands.GeneralLinear (t + 2) ℝ
local notation "U" => GeneralLinear.upperUnipotent (t + 2) ℝ
local notation "Q" => LeftUnipotentQuotient t ℝ
local notation "Q'" => LeftUnipotentQuotient (t + 1) ℝ
local notation "X" => Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ
local notation "Y" => Matrix (Fin (t + 2)) (Fin (t + 2)) ℝ
local notation "pad" => (padGL (R := ℝ) (Nat.le_succ (t + 1)))
local notation "P" => (ArchimedeanLocal.detPower (K := ℝ) realNormalizedAbs)

/-! ### Elementary matrix identities -/

private theorem squareFirstRows_pad_mul' (h : G) (g : H) :
    squareFirstRows (pad h * g).val = h.val * squareFirstRows g.val := by
  ext i j
  change ∑ k, (pad h).val i.castSucc k * g.val k j = ∑ k, h.val i k * g.val k.castSucc j
  rw [Fin.sum_univ_castSucc, UnequalAnalytic.padGL_col _ _ _ (by simp),
    Matrix.one_apply_ne (ne_of_lt i.castSucc_lt_last), zero_mul, add_zero]
  congr 1
  funext k
  rw [UnequalAnalytic.padGL_apply, dite_eq_left ⟨i.isLt, k.isLt⟩]
  rfl

private theorem lastRow_pad_mul' (h : G) (g : H) : lastRow (pad h * g) = lastRow g := by
  funext j
  change ∑ k, (pad h).val (Fin.last m) k * g.val k j = g.val (Fin.last m) j
  simp_rw [UnequalAnalytic.padGL_row _ _ _ (by simp : m ≤ (Fin.last m).val)]
  exact congrArg (fun A : Y => A (Fin.last m) j) (Matrix.one_mul g.val)

private theorem squareFirstRows_mul (A B : Y) :
    squareFirstRows (A * B) = squareFirstRows A * B := by
  ext i j
  rfl

private theorem abs_det_orthogonal' {j : ℕ} (k : unitaryCompact ℝ j) : |k.val.val.det| = 1 := by
  apply (pow_eq_one_iff_of_nonneg (abs_nonneg _) (by decide : 2 ≠ 0)).mp
  have hk : k.val.val * k.val.val.transpose = 1 := by
    rw [← val_inv_of_mem k, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h := congrArg Matrix.det hk
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  rw [pow_two, ← abs_mul, h, abs_one]

private theorem abs_det_torus_mul {j : ℕ} (y : Fin j → ℝ) (k : unitaryCompact ℝ j) :
    |(torus y * (k : Langlands.GeneralLinear j ℝ)).val.det| = Real.exp (∑ i, y i) := by
  rw [Units.val_mul, Matrix.det_mul, abs_mul, abs_det_orthogonal', mul_one, torus_val,
    Matrix.det_diagonal, Real.exp_sum, abs_of_pos (Finset.prod_pos fun i _ => Real.exp_pos _)]

/-- The canonical real quotient representative is a torus element times an
orthogonal matrix, with the toral coordinate of the class. -/
private theorem quotientRepresentative_eq_torus (j : ℕ) (q : LeftUnipotentQuotient j ℝ) :
    quotientRepresentative j q =
      torus (alphaQ q) * (kpart (quotientRepresentative j q) : Langlands.GeneralLinear (j + 1) ℝ) := by
  induction q using Quotient.inductionOn with
  | h g =>
    have hg : quotientRepresentative j (Quotient.mk _ g) =
        torus (alpha g) * (kpart g : Langlands.GeneralLinear (j + 1) ℝ) := by
      rw [quotientRepresentative_mk, inv_mul_eq_iff_eq_mul, ← mul_assoc]
      exact (npart_mul_torus_mul_kpart g).symm
    have hk : kpart (torus (alpha g) * (kpart g : Langlands.GeneralLinear (j + 1) ℝ)) = kpart g := by
      have h := kpart_iwasawa 1 (alpha g) (kpart g)
      rwa [OneMemClass.coe_one, one_mul] at h
    rw [hg, alphaQ_mk, hk]

/-! ### Schwartz decay in triangular entry coordinates -/

private theorem abs_entry_le_norm {l j : Type*} [Fintype l] [Fintype j] (A : Matrix l j ℝ)
    (a : l) (b : j) : |A a b| ≤ ‖A‖ := by
  rw [Matrix.linfty_opNorm_def]
  have h1 : ‖A a b‖₊ ≤ ∑ c, ‖A a c‖₊ :=
    Finset.single_le_sum (f := fun c => ‖A a c‖₊) (fun _ _ => bot_le) (Finset.mem_univ b)
  have h2 : ∑ c, ‖A a c‖₊ ≤ (Finset.univ : Finset l).sup fun i => ∑ c, ‖A i c‖₊ :=
    Finset.le_sup (f := fun i => ∑ c, ‖A i c‖₊) (Finset.mem_univ a)
  have h3 := h1.trans h2
  rw [← Real.norm_eq_abs, ← coe_nnnorm]
  exact_mod_cast h3

private theorem norm_le_card_of_abs_entry_le {l j : Type*} [Fintype l] [Fintype j]
    (A : Matrix l j ℝ) (hA : ∀ a b, |A a b| ≤ 1) : ‖A‖ ≤ Fintype.card j := by
  rw [Matrix.linfty_opNorm_def]
  have h : ((Finset.univ : Finset l).sup fun i => ∑ b, ‖A i b‖₊) ≤ (Fintype.card j : ℝ≥0) := by
    refine Finset.sup_le fun i _ => ?_
    calc
      ∑ b, ‖A i b‖₊ ≤ ∑ _b : j, (1 : ℝ≥0) := Finset.sum_le_sum fun b _ => by
        rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_one]
        exact hA i b
      _ = Fintype.card j := by simp
  exact_mod_cast h

/-- The row of a strictly upper entry position of size `t+2`; it lies among the first
`t+1` rows. -/
private def pairRow (p : UpperEntryPair (t + 2)) : Fin (t + 1) :=
  ⟨p.1.1.val, by
    have h1 : p.1.1.val < p.1.2.val := p.2
    have h2 : p.1.2.val < t + 2 := p.1.2.isLt
    omega⟩

private theorem castSucc_pairRow (p : UpperEntryPair (t + 2)) : (pairRow p).castSucc = p.1.1 :=
  Fin.ext rfl

private theorem conj_eq_entries (η : Fin m → ℝ) (k : unitaryCompact ℝ m) (y : Fin n → ℝ)
    (k' : unitaryCompact ℝ n) (u : U) :
    (k : G).val * ((torus η * (k : G))⁻¹.val *
        squareFirstRows (u.val * (torus y * (k' : H))).val) * ((k' : H)⁻¹).val =
      Matrix.of fun i j => Real.exp (-η i) * u.val.val i.castSucc j * Real.exp (y j) := by
  have h1 : (k : G).val * (torus η * (k : G))⁻¹.val = (torus (-η)).val := by
    rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mul, torus_neg]
  have h2 : squareFirstRows (u.val * (torus y * (k' : H))).val * ((k' : H)⁻¹).val =
      squareFirstRows (u.val.val * (torus y).val) := by
    rw [← mul_assoc, Units.val_mul, squareFirstRows_mul, Matrix.mul_assoc, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.mul_one, Units.val_mul]
  rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc, h2]
  ext i j
  rw [torus_val, Matrix.diagonal_mul, torus_val]
  change Real.exp ((-η) i) * (u.val.val * Matrix.diagonal fun j => Real.exp (y j)) i.castSucc j = _
  rw [Matrix.mul_diagonal, Matrix.of_apply, Pi.neg_apply, mul_assoc]

private theorem upper_diag (u : U) (i : Fin n) : u.val.val i i = 1 := u.property.2 i

/-- The polynomial decay weight of the rectangular block, written in the toral
coordinates of both groups and the strictly upper entries of the unipotent variable. -/
private theorem inv_one_add_norm_pow_le (K : ℕ) (η : Fin m → ℝ) (k : unitaryCompact ℝ m)
    (y : Fin n → ℝ) (k' : unitaryCompact ℝ n) (u : U) :
    ((1 + ‖(torus η * (k : G))⁻¹.val * squareFirstRows (u.val * (torus y * (k' : H))).val‖) ^
        ((m + Fintype.card (UpperEntryPair n)) * K))⁻¹ ≤
      ((m : ℝ) * n) ^ ((m + Fintype.card (UpperEntryPair n)) * K) *
        ((∏ i : Fin m, ((1 + Real.exp (y i.castSucc - η i)) ^ K)⁻¹) *
          ∏ p : UpperEntryPair n,
            ((1 + Real.exp (y p.1.2 - η (pairRow p)) * |u.val.val p.1.1 p.1.2|) ^ K)⁻¹) := by
  set K' := (m + Fintype.card (UpperEntryPair n)) * K with hK'
  set c : ℝ := (m : ℝ) * n with hc
  have hc1 : 1 ≤ c := by
    rw [hc]
    have h1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.succ_pos t
    have h2 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.succ_pos (t + 1)
    nlinarith
  set M : X := (torus η * (k : G))⁻¹.val * squareFirstRows (u.val * (torus y * (k' : H))).val
    with hM
  set N : X := Matrix.of fun i j => Real.exp (-η i) * u.val.val i.castSucc j * Real.exp (y j)
    with hN
  have hkM : ‖(k : G).val‖ ≤ m := by
    have := norm_le_card_of_abs_entry_le (k : G).val
      (fun a b => RealWhittakerGauge.abs_unitary_entry_le k a b)
    simpa using this
  have hkM' : ‖((k' : H)⁻¹).val‖ ≤ n := by
    have := norm_le_card_of_abs_entry_le ((k' : H)⁻¹).val
      (fun a b => RealWhittakerGauge.abs_unitary_inv_entry_le k' a b)
    simpa using this
  have hNM : ‖N‖ ≤ c * ‖M‖ := by
    rw [hN, ← conj_eq_entries η k y k' u]
    calc
      ‖(k : G).val * M * ((k' : H)⁻¹).val‖ ≤ ‖(k : G).val‖ * ‖M‖ * ‖((k' : H)⁻¹).val‖ :=
        (Matrix.linfty_opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (Matrix.linfty_opNorm_mul _ _) (norm_nonneg _))
      _ ≤ (m : ℝ) * ‖M‖ * n := by gcongr
      _ = c * ‖M‖ := by rw [hc]; ring
  have h1N : 1 + ‖N‖ ≤ c * (1 + ‖M‖) := by nlinarith [norm_nonneg M]
  have hdiag : ∀ i : Fin m, 1 + Real.exp (y i.castSucc - η i) ≤ 1 + ‖N‖ := by
    intro i
    have h := abs_entry_le_norm N i i.castSucc
    rw [hN, Matrix.of_apply, upper_diag, mul_one, ← Real.exp_add, abs_of_pos (Real.exp_pos _)] at h
    rw [show y i.castSucc - η i = -η i + y i.castSucc by ring]
    linarith
  have hpair : ∀ p : UpperEntryPair n,
      1 + Real.exp (y p.1.2 - η (pairRow p)) * |u.val.val p.1.1 p.1.2| ≤ 1 + ‖N‖ := by
    intro p
    have h := abs_entry_le_norm N (pairRow p) p.1.2
    rw [hN, Matrix.of_apply, castSucc_pairRow, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_pos (Real.exp_pos _)] at h
    have he : Real.exp (y p.1.2 - η (pairRow p)) * |u.val.val p.1.1 p.1.2| =
        Real.exp (-η (pairRow p)) * |u.val.val p.1.1 p.1.2| * Real.exp (y p.1.2) := by
      rw [show y p.1.2 - η (pairRow p) = -η (pairRow p) + y p.1.2 by ring, Real.exp_add]
      ring
    rw [he]
    linarith
  set A : ℝ := (∏ i : Fin m, (1 + Real.exp (y i.castSucc - η i)) ^ K) *
    ∏ p : UpperEntryPair n, (1 + Real.exp (y p.1.2 - η (pairRow p)) * |u.val.val p.1.1 p.1.2|) ^ K
    with hA
  have hA0 : 0 < A := by
    rw [hA]
    refine mul_pos (Finset.prod_pos fun i _ => by positivity) (Finset.prod_pos fun p _ => ?_)
    positivity
  have hAN : A ≤ (1 + ‖N‖) ^ K' := by
    rw [hA, Finset.prod_pow, Finset.prod_pow, ← mul_pow, hK', mul_comm _ K, pow_mul', pow_add]
    gcongr
    · calc
        ∏ i : Fin m, (1 + Real.exp (y i.castSucc - η i)) ≤ ∏ _i : Fin m, (1 + ‖N‖) :=
          Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => hdiag i)
        _ = (1 + ‖N‖) ^ m := by simp
    · calc
        ∏ p : UpperEntryPair n, (1 + Real.exp (y p.1.2 - η (pairRow p)) * |u.val.val p.1.1 p.1.2|)
            ≤ ∏ _p : UpperEntryPair n, (1 + ‖N‖) :=
          Finset.prod_le_prod₀ (fun p _ => by positivity) (fun p _ => hpair p)
        _ = (1 + ‖N‖) ^ Fintype.card (UpperEntryPair n) := by simp
  have hinv : (∏ i : Fin m, ((1 + Real.exp (y i.castSucc - η i)) ^ K)⁻¹) *
      ∏ p : UpperEntryPair n,
        ((1 + Real.exp (y p.1.2 - η (pairRow p)) * |u.val.val p.1.1 p.1.2|) ^ K)⁻¹ = A⁻¹ := by
    rw [hA, mul_inv, Finset.prod_inv_distrib, Finset.prod_inv_distrib]
  have hM0 : 0 < (1 + ‖M‖) ^ K' := by positivity
  rw [hinv, ← one_div, ← div_eq_mul_inv, div_le_div_iff₀ hM0 hA0, one_mul]
  calc
    A ≤ (1 + ‖N‖) ^ K' := hAN
    _ ≤ (c * (1 + ‖M‖)) ^ K' := by gcongr
    _ = c ^ K' * (1 + ‖M‖) ^ K' := mul_pow _ _ _

private theorem norm_squareFirstRows_le (A : Y) : ‖squareFirstRows A‖ ≤ ‖A‖ := by
  rw [Matrix.linfty_opNorm_def, Matrix.linfty_opNorm_def]
  refine NNReal.coe_le_coe.mpr (Finset.sup_le fun i _ => ?_)
  exact Finset.le_sup (f := fun i => ∑ j, ‖A i j‖₊) (Finset.mem_univ i.castSucc)

private theorem norm_lastRow_le (g : H) : ‖lastRow g‖ ≤ ‖g.val‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => ?_
  rw [Real.norm_eq_abs]
  exact abs_entry_le_norm g.val (Fin.last m) j

/-- Schwartz decay of a square test splits into decay of its first rows and of its
last row. -/
private theorem norm_schwartz_le_split (Ψ : 𝓢(Y, ℂ)) (K₁ K₂ : ℕ) (g : H) :
    ‖Ψ g.val‖ ≤ 2 ^ (K₁ + K₂) * (Finset.Iic (K₁ + K₂, 0)).sup
        (fun q : ℕ × ℕ => SchwartzMap.seminorm ℝ q.1 q.2) Ψ *
      (((1 + ‖squareFirstRows g.val‖) ^ K₁)⁻¹ * ((1 + ‖lastRow g‖) ^ K₂)⁻¹) := by
  set S := 2 ^ (K₁ + K₂) * (Finset.Iic (K₁ + K₂, 0)).sup
    (fun q : ℕ × ℕ => SchwartzMap.seminorm ℝ q.1 q.2) Ψ with hS
  have hdecay : (1 + ‖g.val‖) ^ (K₁ + K₂) * ‖Ψ g.val‖ ≤ S := by
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (show K₁ + K₂ ≤ (K₁ + K₂, 0).1 from le_rfl) (show 0 ≤ (K₁ + K₂, 0).2 from le_rfl) Ψ g.val
    rwa [norm_iteratedFDeriv_zero] at h
  have h1 : (1 + ‖squareFirstRows g.val‖) ^ K₁ ≤ (1 + ‖g.val‖) ^ K₁ := by
    gcongr
    exact norm_squareFirstRows_le g.val
  have h2 : (1 + ‖lastRow g‖) ^ K₂ ≤ (1 + ‖g.val‖) ^ K₂ := by
    gcongr
    exact norm_lastRow_le g
  have hp1 : 0 < (1 + ‖squareFirstRows g.val‖) ^ K₁ := by positivity
  have hp2 : 0 < (1 + ‖lastRow g‖) ^ K₂ := by positivity
  rw [← mul_inv, ← div_eq_mul_inv, le_div_iff₀ (mul_pos hp1 hp2)]
  calc
    ‖Ψ g.val‖ * ((1 + ‖squareFirstRows g.val‖) ^ K₁ * (1 + ‖lastRow g‖) ^ K₂) ≤
        ‖Ψ g.val‖ * ((1 + ‖g.val‖) ^ K₁ * (1 + ‖g.val‖) ^ K₂) := by gcongr
    _ = (1 + ‖g.val‖) ^ (K₁ + K₂) * ‖Ψ g.val‖ := by rw [pow_add]; ring
    _ ≤ S := hdecay

/-! ### Integration over the strictly upper entries -/

private theorem integrable_entry_decay (ν : Measure ℝ) [ν.IsAddHaarMeasure] (K : ℕ)
    (hK : 2 ≤ K) : Integrable (fun v : ℝ => ((1 + |v|) ^ K)⁻¹) ν := by
  have h : (fun v : ℝ => ((1 + |v|) ^ K)⁻¹) = fun v => (1 + ‖v‖) ^ (-(K : ℝ)) := by
    funext v
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, Real.norm_eq_abs]
  rw [h]
  apply integrable_one_add_norm
  rw [Module.finrank_self]
  exact_mod_cast (by omega : 1 < K)

private theorem integral_entry_decay (ν : Measure ℝ) [ν.IsAddHaarMeasure] (K : ℕ) (hK : 2 ≤ K)
    (l : ℝ) :
    Integrable (fun v : ℝ => ((1 + Real.exp l * |v|) ^ K)⁻¹) ν ∧
      ∫ v, ((1 + Real.exp l * |v|) ^ K)⁻¹ ∂ν = Real.exp (-l) * ∫ v, ((1 + |v|) ^ K)⁻¹ ∂ν := by
  have hcomp : (fun v : ℝ => ((1 + Real.exp l * |v|) ^ K)⁻¹) =
      fun v => (fun w : ℝ => ((1 + |w|) ^ K)⁻¹) (Real.exp l • v) := by
    funext v
    simp only [smul_eq_mul, abs_mul, abs_of_pos (Real.exp_pos l)]
  rw [hcomp]
  refine ⟨(integrable_entry_decay ν K hK).comp_smul (Real.exp_pos l).ne', ?_⟩
  rw [Measure.integral_comp_smul ν (fun w : ℝ => ((1 + |w|) ^ K)⁻¹) (Real.exp l), Module.finrank_self, pow_one, smul_eq_mul,
    abs_of_pos (inv_pos.mpr (Real.exp_pos l)), Real.exp_neg]

/-- Integration of the entrywise decay over the self-dual entry product on the upper
unipotent group: each entry contributes the inverse of its scaling factor. -/
private theorem lintegral_upperStep_entry_decay (j : ℕ) (b : ℝˣ) (K : ℕ) (hK : 2 ≤ K)
    (l : UpperEntryPair (j + 1) → ℝ) :
    ∫⁻ u, ENNReal.ofReal
        (∏ p, ((1 + Real.exp (l p) * |upperEntryCoordinates (j + 1) u p|) ^ K)⁻¹)
        ∂upperStepHaar j b =
      ENNReal.ofReal ((∫ v, ((1 + |v|) ^ K)⁻¹ ∂(realSelfDualMeasure b).measure) ^
        Fintype.card (UpperEntryPair (j + 1)) * Real.exp (-∑ p, l p)) := by
  set ν := (realSelfDualMeasure b).measure with hν
  have hc : Continuous fun (z : UpperEntryPair (j + 1) → ℝ) =>
      ∏ p, ((1 + Real.exp (l p) * |z p|) ^ K)⁻¹ := by
    refine continuous_finsetProd _ fun p _ => ?_
    refine Continuous.inv₀ (by fun_prop) fun z => ?_
    have : 0 < 1 + Real.exp (l p) * |z p| := by positivity
    exact (pow_pos this K).ne'
  have hf : Measurable fun u : GeneralLinear.upperUnipotent (j + 1) ℝ => ENNReal.ofReal
      (∏ p, ((1 + Real.exp (l p) * |upperEntryCoordinates (j + 1) u p|) ^ K)⁻¹) :=
    ENNReal.measurable_ofReal.comp
      ((hc.comp (upperEntryCoordinates (j + 1) (K := ℝ)).continuous).measurable)
  rw [upperStepHaar, lintegral_map hf
    (upperEntryCoordinates (j + 1) (K := ℝ)).symm.continuous.measurable]
  simp only [Homeomorph.apply_symm_apply]
  have hint : Integrable (fun (z : UpperEntryPair (j + 1) → ℝ) =>
      ∏ p, ((1 + Real.exp (l p) * |z p|) ^ K)⁻¹) (Measure.pi fun _ => ν) :=
    Integrable.fintype_prod (f := fun p v => ((1 + Real.exp (l p) * |v|) ^ K)⁻¹)
      fun p => (integral_entry_decay ν K hK (l p)).1
  rw [upperEntryProductMeasure, ← hν, ← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun z => by positivity),
    integral_fintype_prod_eq_prod (𝕜 := ℝ) (fun p v => ((1 + Real.exp (l p) * |v|) ^ K)⁻¹)]
  congr 1
  simp_rw [(integral_entry_decay ν K hK _).2]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum,
    Finset.sum_neg_distrib, mul_comm]

/-! ### Integration over the smaller quotient -/

/-- One toral coordinate: the dominant exponent and the decay of the diagonal entry
give two-sided exponential decay. -/
private theorem coord_decay {α c x : ℝ} {K : ℕ} (hc : α + 1 ≤ c) (hK : α + c + 1 ≤ K) :
    Real.exp (α * |x| - c * x) * ((1 + Real.exp (-x)) ^ K)⁻¹ ≤ Real.exp (-|x|) := by
  have hpos : 0 < (1 + Real.exp (-x)) ^ K := by positivity
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    have h1 : ((1 + Real.exp (-x)) ^ K)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [Real.exp_pos (-x)]))
    calc
      _ ≤ Real.exp (α * x - c * x) * 1 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ ≤ _ := by
        rw [mul_one]
        exact Real.exp_le_exp.mpr (by nlinarith)
  · rw [abs_of_neg hx]
    have h1 : Real.exp (-x) ^ K ≤ (1 + Real.exp (-x)) ^ K :=
      pow_le_pow_left₀ (Real.exp_pos _).le (by linarith [Real.exp_pos (-x)]) K
    have h2 : ((1 + Real.exp (-x)) ^ K)⁻¹ ≤ Real.exp (K * x) := by
      calc
        ((1 + Real.exp (-x)) ^ K)⁻¹ ≤ (Real.exp (-x) ^ K)⁻¹ := inv_anti₀ (by positivity) h1
        _ = Real.exp (K * x) := by
          rw [← Real.exp_nat_mul, ← Real.exp_neg]
          ring_nf
    calc
      _ ≤ Real.exp (α * -x - c * x) * Real.exp (K * x) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = Real.exp (α * -x - c * x + K * x) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (-(-x)) := Real.exp_le_exp.mpr (by nlinarith)

private theorem sum_abs_castSucc_le (y : Fin n → ℝ) : ∑ i : Fin m, |y i.castSucc| ≤ ∑ j, |y j| := by
  rw [Fin.sum_univ_castSucc (fun j => |y j|)]
  linarith [abs_nonneg (y (Fin.last m))]

private theorem sum_pairRow_le (η : Fin m → ℝ) :
    ∑ p : UpperEntryPair n, η (pairRow p) ≤ Fintype.card (UpperEntryPair n) * ∑ i, |η i| := by
  calc
    ∑ p : UpperEntryPair n, η (pairRow p) ≤ ∑ _p : UpperEntryPair n, ∑ i, |η i| :=
      Finset.sum_le_sum fun p _ => (le_abs_self _).trans
        (Finset.single_le_sum (f := fun i => |η i|) (fun i _ => abs_nonneg _) (Finset.mem_univ _))
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

private theorem sum_abs_add_le (x z : Fin m → ℝ) :
    ∑ i, |(x + z) i| ≤ ∑ i, |x i| + ∑ i, |z i| := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => abs_add_le _ _

/-- The integral over the smaller quotient of the gauge of the smaller Whittaker
function, the determinant factor and the diagonal decay, after translating the
toral coordinates by the first coordinates of the larger torus. -/
private theorem lintegral_quotient_bound {ν : Measure Q} {κ : ℝ≥0} {L : (Fin m → ℝ) →L[ℝ] ℝ}
    (hκL : ∀ B : (Fin m → ℝ) → ℝ≥0∞, Measurable B →
      ∫⁻ q, B (alphaQ q) ∂ν = (κ : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (Real.exp (L x)) * B x)
    (W : G → ℂ) {N CW : ℝ} (hCW : 0 ≤ CW) (hN : 0 ≤ N)
    (hW : ∀ (η : Fin m → ℝ) (k : unitaryCompact ℝ m),
      ‖W (torus η * (k : G))‖ ≤ CW * Real.exp (N * ∑ i, |η i|))
    {c : ℝ} {K : ℕ} (hc : ‖L‖ + N + Fintype.card (UpperEntryPair n) + 1 ≤ c)
    (hK : ‖L‖ + N + Fintype.card (UpperEntryPair n) + c + 1 ≤ K) (y : Fin n → ℝ) :
    ∫⁻ q, ENNReal.ofReal (‖W (quotientRepresentative t q)‖ * Real.exp (-c * ∑ i, alphaQ q i) *
        (∏ i : Fin m, ((1 + Real.exp (y i.castSucc - alphaQ q i)) ^ K)⁻¹) *
        Real.exp (∑ p : UpperEntryPair n, alphaQ q (pairRow p))) ∂ν ≤
      (κ : ℝ≥0∞) * (ENNReal.ofReal (CW * Real.exp ((‖L‖ + N + Fintype.card (UpperEntryPair n)) *
          ∑ j, |y j| - c * ∑ i : Fin m, y i.castSucc)) *
        ∫⁻ x : Fin m → ℝ, ENNReal.ofReal (Real.exp (-1 * ∑ i, |x i|))) := by
  set cardP : ℝ := (Fintype.card (UpperEntryPair n) : ℝ) with hcardP
  set α : ℝ := ‖L‖ + N + cardP with hα
  have hP0 : 0 ≤ cardP := Nat.cast_nonneg _
  have hα0 : 0 ≤ α := by rw [hα]; positivity
  set z : Fin m → ℝ := fun i => y i.castSucc with hz
  let F : (Fin m → ℝ) → ℝ := fun η => CW * Real.exp (N * ∑ i, |η i|) * Real.exp (-c * ∑ i, η i) *
    (∏ i : Fin m, ((1 + Real.exp (z i - η i)) ^ K)⁻¹) *
    Real.exp (∑ p : UpperEntryPair n, η (pairRow p))
  have hFc : Continuous F := by
    have hprod : Continuous fun η : Fin m → ℝ => ∏ i : Fin m, ((1 + Real.exp (z i - η i)) ^ K)⁻¹ := by
      refine continuous_finsetProd _ fun i _ => ?_
      refine Continuous.inv₀ (by fun_prop) fun η => ?_
      have : 0 < 1 + Real.exp (z i - η i) := by positivity
      exact (pow_pos this K).ne'
    have h1 : Continuous fun η : Fin m → ℝ => ∑ i, |η i| :=
      continuous_finsetSum _ fun i _ => (continuous_apply i).abs
    have h2 : Continuous fun η : Fin m → ℝ => ∑ i, η i :=
      continuous_finsetSum _ fun i _ => continuous_apply i
    have h3 : Continuous fun η : Fin m → ℝ => ∑ p : UpperEntryPair n, η (pairRow p) :=
      continuous_finsetSum _ fun p _ => continuous_apply _
    exact (((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul h1))).mul
      (Real.continuous_exp.comp (continuous_const.mul h2))).mul hprod).mul
      (Real.continuous_exp.comp h3)
  let B : (Fin m → ℝ) → ℝ≥0∞ := fun η => ENNReal.ofReal (F η)
  have hBm : Measurable B := ENNReal.measurable_ofReal.comp hFc.measurable
  have hpt : ∀ q : Q, ENNReal.ofReal (‖W (quotientRepresentative t q)‖ *
      Real.exp (-c * ∑ i, alphaQ q i) *
      (∏ i : Fin m, ((1 + Real.exp (y i.castSucc - alphaQ q i)) ^ K)⁻¹) *
      Real.exp (∑ p : UpperEntryPair n, alphaQ q (pairRow p))) ≤ B (alphaQ q) := by
    intro q
    refine ENNReal.ofReal_le_ofReal ?_
    have hWq := hW (alphaQ q) (kpart (quotientRepresentative t q))
    rw [← quotientRepresentative_eq_torus] at hWq
    have hprod : 0 ≤ ∏ i : Fin m, ((1 + Real.exp (y i.castSucc - alphaQ q i)) ^ K)⁻¹ :=
      Finset.prod_nonneg fun i _ => by positivity
    dsimp only [F]
    gcongr
  have hkey : ∀ x : Fin m → ℝ, ENNReal.ofReal (Real.exp (L (x + z))) * B (x + z) ≤
      ENNReal.ofReal (CW * Real.exp (α * ∑ j, |y j| - c * ∑ i : Fin m, y i.castSucc)) *
        ENNReal.ofReal (Real.exp (-1 * ∑ i, |x i|)) := by
    intro x
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    set Pr := ∏ i : Fin m, ((1 + Real.exp (-x i)) ^ K)⁻¹ with hPr
    have hPr0 : 0 ≤ Pr := Finset.prod_nonneg fun i _ => by positivity
    have hprod : (∏ i : Fin m, ((1 + Real.exp (z i - (x + z) i)) ^ K)⁻¹) = Pr := by
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Pi.add_apply, show z i - (x i + z i) = -x i by ring]
    set Sx := ∑ i, |x i| with hSx
    set Sz := ∑ i, |z i| with hSz
    have e1 : L (x + z) ≤ ‖L‖ * (Sx + Sz) :=
      (RealEqualConvergence.linear_le L (x + z)).trans (mul_le_mul_of_nonneg_left (sum_abs_add_le x z) (norm_nonneg _))
    have e2 : N * ∑ i, |(x + z) i| ≤ N * (Sx + Sz) := mul_le_mul_of_nonneg_left (sum_abs_add_le x z) hN
    have e3 : ∑ p : UpperEntryPair n, (x + z) (pairRow p) ≤ cardP * (Sx + Sz) :=
      (sum_pairRow_le (x + z)).trans (mul_le_mul_of_nonneg_left (sum_abs_add_le x z) hP0)
    have e4 : Sz ≤ ∑ j, |y j| := sum_abs_castSucc_le y
    have e5 : ∑ i, (x + z) i = ∑ i, x i + ∑ i : Fin m, y i.castSucc := by
      rw [← Finset.sum_add_distrib]
      rfl
    have hexp : L (x + z) + N * ∑ i, |(x + z) i| + -c * ∑ i, (x + z) i +
        ∑ p : UpperEntryPair n, (x + z) (pairRow p) ≤
        (α * Sx - c * ∑ i, x i) + (α * ∑ j, |y j| - c * ∑ i : Fin m, y i.castSucc) := by
      rw [e5]
      have : α * Sz ≤ α * ∑ j, |y j| := mul_le_mul_of_nonneg_left e4 hα0
      rw [hα] at this ⊢
      nlinarith
    have hcoord : Real.exp (α * Sx - c * ∑ i, x i) * Pr ≤ Real.exp (-1 * Sx) := by
      have hsplit : Real.exp (α * Sx - c * ∑ i, x i) =
          ∏ i : Fin m, Real.exp (α * |x i| - c * x i) := by
        rw [← Real.exp_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rw [hsplit, hPr, ← Finset.prod_mul_distrib, neg_one_mul, hSx, ← Finset.sum_neg_distrib,
        Real.exp_sum]
      exact Finset.prod_le_prod₀ (fun i _ => by positivity)
        (fun i _ => coord_decay (by rw [hα]; linarith) (by rw [hα]; linarith))
    dsimp only [B, F]
    rw [hprod]
    calc
      Real.exp (L (x + z)) * (CW * Real.exp (N * ∑ i, |(x + z) i|) *
          Real.exp (-c * ∑ i, (x + z) i) * Pr * Real.exp (∑ p : UpperEntryPair n, (x + z) (pairRow p)))
          = CW * (Real.exp (L (x + z) + N * ∑ i, |(x + z) i| + -c * ∑ i, (x + z) i +
              ∑ p : UpperEntryPair n, (x + z) (pairRow p)) * Pr) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_add]
        ring
      _ ≤ CW * (Real.exp ((α * Sx - c * ∑ i, x i) +
            (α * ∑ j, |y j| - c * ∑ i : Fin m, y i.castSucc)) * Pr) := by
        gcongr
      _ = CW * Real.exp (α * ∑ j, |y j| - c * ∑ i : Fin m, y i.castSucc) *
            (Real.exp (α * Sx - c * ∑ i, x i) * Pr) := by
        rw [Real.exp_add]
        ring
      _ ≤ CW * Real.exp (α * ∑ j, |y j| - c * ∑ i : Fin m, y i.castSucc) * Real.exp (-1 * Sx) := by
        gcongr
  calc
    _ ≤ ∫⁻ q, B (alphaQ q) ∂ν := lintegral_mono hpt
    _ = (κ : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (Real.exp (L x)) * B x := hκL B hBm
    _ = (κ : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (Real.exp (L (x + z))) * B (x + z) := by
      rw [lintegral_add_right_eq_self (fun x => ENNReal.ofReal (Real.exp (L x)) * B x) z]
    _ ≤ (κ : ℝ≥0∞) * ∫⁻ x : Fin m → ℝ, ENNReal.ofReal (CW * Real.exp (α * ∑ j, |y j| -
          c * ∑ i : Fin m, y i.castSucc)) * ENNReal.ofReal (Real.exp (-1 * ∑ i, |x i|)) := by
      gcongr (κ : ℝ≥0∞) * ?_
      exact lintegral_mono fun x => hkey x
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]


/-! ### The Fubini chart of `RealLocalEqualUnfolding` -/

private theorem continuous_representative' (j : ℕ) : Continuous (quotientRepresentative j) := by
  have h : quotientRepresentative j =
      (unipotentQuotientHomeomorph j) ∘ (fun q : LeftUnipotentQuotient j ℝ => (1, q)) := by
    funext q
    change _ = (1 : Langlands.GeneralLinear (j + 1) ℝ) * quotientRepresentative j q
    exact (one_mul _).symm
  rw [h]
  exact (unipotentQuotientHomeomorph j).continuous.comp (continuous_const.prodMk continuous_id)

private local instance (j : ℕ) : LocallyCompactSpace (Langlands.GeneralLinear (j + 1) ℝ) := by
  let _ : LocallyCompactSpace (Matrix (Fin (j + 1)) (Fin (j + 1)) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin (j + 1) → Fin (j + 1) → ℝ))
  exact Units.isOpenEmbedding_val.locallyCompactSpace

private local instance (j : ℕ) : SecondCountableTopology (Langlands.GeneralLinear (j + 1) ℝ) :=
  Units.isOpenEmbedding_val.isInducing.secondCountableTopology

private local instance (j : ℕ) : SigmaCompactSpace (LeftUnipotentQuotient j ℝ) := by
  apply isSigmaCompact_univ_iff.mp
  rw [← Set.range_eq_univ.mpr (Quotient.mk_surjective
    (s := QuotientGroup.rightRel (GeneralLinear.upperUnipotent (j + 1) ℝ)))]
  exact isSigmaCompact_range continuous_quotient_mk'

private local instance (j : ℕ) : SigmaCompactSpace (GeneralLinear.upperUnipotent (j + 1) ℝ) := by
  have h : IsClosed (GeneralLinear.upperUnipotent (j + 1) ℝ : Set (Langlands.GeneralLinear (j + 1) ℝ)) :=
    UpperUnipotent.isClosed
  exact h.isClosedEmbedding_subtypeVal.sigmaCompactSpace

private local instance (j : ℕ) : LocallyCompactSpace (GeneralLinear.upperUnipotent (j + 1) ℝ) := by
  have h : IsClosed (GeneralLinear.upperUnipotent (j + 1) ℝ : Set (Langlands.GeneralLinear (j + 1) ℝ)) :=
    UpperUnipotent.isClosed
  exact h.isClosedEmbedding_subtypeVal.locallyCompactSpace

private local instance (j : ℕ) : SecondCountableTopology (GeneralLinear.upperUnipotent (j + 1) ℝ) :=
  Topology.IsInducing.subtypeVal.secondCountableTopology

variable (t) in
private def equalUnfoldingShift : Q × H ≃ᵐ Q × H where
  toFun p := (p.1, (pad (quotientRepresentative t p.1))⁻¹ * p.2)
  invFun p := (p.1, pad (quotientRepresentative t p.1) * p.2)
  left_inv p := by simp
  right_inv p := by simp
  measurable_toFun := measurable_fst.prodMk (((UnequalAnalytic.continuous_padGL _).comp
    ((continuous_representative' t).comp continuous_fst)).inv.mul continuous_snd).measurable
  measurable_invFun := measurable_fst.prodMk (((UnequalAnalytic.continuous_padGL _).comp
    ((continuous_representative' t).comp continuous_fst)).mul continuous_snd).measurable

private theorem measurePreserving_equalUnfoldingShift (D : RealQuotientMeasureData t)
    (D' : RealQuotientMeasureData (t + 1)) :
    MeasurePreserving (equalUnfoldingShift t) (D.measure.prod D'.groupHaar)
      (D.measure.prod D'.groupHaar) := by
  let := D.unipotentHaar_rightInvariant
  let := D.compatible.regular
  let := D'.groupHaar_isHaar
  refine (MeasurePreserving.id D.measure).skew_product
    (g := fun q g => (pad (quotientRepresentative t q))⁻¹ * g) ?_ ?_
  · exact measurable_snd.comp (equalUnfoldingShift t).measurable
  · exact Filter.Eventually.of_forall fun q => map_mul_left_eq_self D'.groupHaar
      (pad (quotientRepresentative t q))⁻¹

variable (t) in
private def equalUnfoldingChart : Q' × (Q × U) ≃ᵐ Q × H :=
  MeasurableEquiv.prodComm.trans (MeasurableEquiv.prodAssoc.trans (
    ((MeasurableEquiv.refl Q).prodCongr (unipotentQuotientHomeomorph (t + 1)).toMeasurableEquiv).trans
    (equalUnfoldingShift t)))

private theorem measurePreserving_equalUnfoldingChart (D : RealQuotientMeasureData t)
    (D' : RealQuotientMeasureData (t + 1)) :
    MeasurePreserving (equalUnfoldingChart t) (D'.measure.prod (D.measure.prod D'.unipotentHaar))
      (D.measure.prod D'.groupHaar) := by
  let := D.unipotentHaar_rightInvariant
  let := D'.unipotentHaar_rightInvariant
  let := D.compatible.regular
  let := D'.compatible.regular
  let := D'.unipotentHaar_isHaar
  exact (measurePreserving_equalUnfoldingShift D D').comp
    (((MeasurePreserving.id D.measure).prod (measurePreserving_unipotentQuotient D')).comp
      ((measurePreserving_prodAssoc D.measure D'.unipotentHaar D'.measure).comp
        Measure.measurePreserving_swap))

private theorem equalUnfoldingChart_apply (q' : Q') (q : Q) (u : U) :
    equalUnfoldingChart t (q', (q, u)) =
      (q, (pad (quotientRepresentative t q))⁻¹ * (u.val * quotientRepresentative (t + 1) q')) :=
  rfl

/-! ### Size of the unfolded kernel at the chart -/

private theorem detPower_eq_cpow' {j : ℕ} (g : Langlands.GeneralLinear j ℝ) (s : ℂ) :
    P g s = ((|g.val.det| : ℝ) : ℂ) ^ s := by
  have h : (|(g.val.det)| : ℝ) ≠ 0 := abs_ne_zero.mpr (determinant g).ne_zero
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr h), ← Complex.ofReal_log (abs_nonneg _)]
  exact congrArg Complex.exp (mul_comm _ _)

private theorem determinantWeight_comp_pad' (d : RealCharacterData) (s : ℂ) (g : G) :
    determinantWeight d s (pad g) = determinantWeight d s g := by
  unfold determinantWeight
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
  congr 1
  exact Units.ext (UnequalAnalytic.det_padGL _ g)

private theorem determinantWeight_unip_mul' (d : RealCharacterData) (s : ℂ) (u : U) (g : H) :
    determinantWeight d s (u.val * g) = determinantWeight d s g := by
  have hu : determinant u.val = 1 := Units.ext (unipotent_det u)
  have h : determinant (u.val * g) = determinant g := by
    rw [map_mul, hu, one_mul]
  simp only [determinantWeight, MonoidHom.comp_apply, h]

private theorem abs_det_representative (j : ℕ) (q : LeftUnipotentQuotient j ℝ) :
    |(quotientRepresentative j q).val.det| = Real.exp (∑ i, alphaQ q i) := by
  rw [quotientRepresentative_eq_torus, abs_det_torus_mul]

private theorem norm_determinantWeight_representative (d : RealCharacterData) (z : ℂ) (j : ℕ)
    (q : LeftUnipotentQuotient j ℝ) :
    ‖determinantWeight d z (quotientRepresentative j q)‖ =
      Real.exp ((d.exponent.re + z.re) * ∑ i, alphaQ q i) := by
  rw [norm_determinantWeight_real, abs_det_representative, ← Real.exp_mul, mul_comm]

private theorem norm_detPower_representative (z : ℂ) (j : ℕ) (q : LeftUnipotentQuotient j ℝ) :
    ‖P (quotientRepresentative j q) z‖ = Real.exp (z.re * ∑ i, alphaQ q i) := by
  have hpos : 0 < |(quotientRepresentative j q).val.det| :=
    abs_pos.mpr (determinant (quotientRepresentative j q)).ne_zero
  rw [detPower_eq_cpow', Complex.norm_cpow_eq_rpow_re_of_pos hpos, abs_det_representative,
    ← Real.exp_mul, mul_comm]

/-- The size of the unfolded kernel at a point of the Fubini chart: the test at the
shifted point, the larger Whittaker function at the larger representative with the
determinant power, and the smaller one with the dominant power. -/
private theorem norm_kernel_chart (d : RealCharacterData) (Ψ : Y → ℂ) (W : G → ℂ) (V : H → ℂ)
    (hVu : ∀ (u : U) (g : H), ‖V (u.val * g)‖ = ‖V g‖) (s : ℂ) (q' : Q') (q : Q) (u : U) :
    ‖equalUnfoldedKernel d Ψ W V s (equalUnfoldingChart t (q', (q, u)))‖ =
      ‖Ψ ((pad (quotientRepresentative t q))⁻¹ * (u.val * quotientRepresentative (t + 1) q')).val‖ *
        (‖V (quotientRepresentative (t + 1) q')‖ *
          Real.exp ((d.exponent.re + s.re + ((t : ℝ) + 1) / 2) * ∑ j, alphaQ q' j)) *
        (‖W (quotientRepresentative t q)‖ *
          Real.exp (-(d.exponent.re + ((t : ℝ) + 2) / 2) * ∑ i, alphaQ q i)) := by
  have hshift : pad (quotientRepresentative t q) * ((pad (quotientRepresentative t q))⁻¹ *
      (u.val * quotientRepresentative (t + 1) q')) = u.val * quotientRepresentative (t + 1) q' :=
    mul_inv_cancel_left _ _
  have hdet : ∀ z : ℂ, determinantWeight d z ((pad (quotientRepresentative t q))⁻¹ *
      (u.val * quotientRepresentative (t + 1) q')) =
      (determinantWeight d z (quotientRepresentative t q))⁻¹ *
        determinantWeight d z (quotientRepresentative (t + 1) q') := by
    intro z
    rw [map_mul, map_inv, determinantWeight_comp_pad', determinantWeight_unip_mul']
  have hre : (s + (m : ℂ) / 2).re = s.re + ((t : ℝ) + 1) / 2 := by simp
  have hre' : (s - 1 / 2).re = s.re - 1 / 2 := by simp
  rw [equalUnfoldingChart_apply]
  simp only [equalUnfoldedKernel]
  rw [hshift, hdet, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_inv, hVu,
    norm_determinantWeight_representative, norm_determinantWeight_representative,
    norm_detPower_representative, hre, hre', ← Real.exp_neg,
    show Real.exp ((d.exponent.re + s.re + ((t : ℝ) + 1) / 2) * ∑ j, alphaQ q' j) =
      Real.exp ((d.exponent.re + (s.re + ((t : ℝ) + 1) / 2)) * ∑ j, alphaQ q' j) by
        congr 1; ring,
    show Real.exp (-(d.exponent.re + ((t : ℝ) + 2) / 2) * ∑ i, alphaQ q i) =
      Real.exp (-((d.exponent.re + (s.re + ((t : ℝ) + 1) / 2)) * ∑ i, alphaQ q i)) *
        Real.exp ((s.re - 1 / 2) * ∑ i, alphaQ q i) by
        rw [← Real.exp_add]; congr 1; ring]
  ring

/-- Pointwise majorant of the unfolded kernel at the chart, separated into the test
seminorm, a function of the larger class, a function of both classes, and the
entrywise decay in the unipotent variable. -/
private theorem norm_kernel_chart_le (d : RealCharacterData) (Ψ : 𝓢(Y, ℂ)) (W : G → ℂ)
    (V : H → ℂ) (hVu : ∀ (u : U) (g : H), ‖V (u.val * g)‖ = ‖V g‖) (s : ℂ) (K K₂ : ℕ)
    (q' : Q') (q : Q) (u : U) :
    ‖equalUnfoldedKernel d Ψ W V s (equalUnfoldingChart t (q', (q, u)))‖ ≤
      (Finset.Iic ((m + Fintype.card (UpperEntryPair n)) * K + K₂, 0)).sup
          (fun r : ℕ × ℕ => SchwartzMap.seminorm ℝ r.1 r.2) Ψ *
        (2 ^ ((m + Fintype.card (UpperEntryPair n)) * K + K₂) *
          ((m : ℝ) * n) ^ ((m + Fintype.card (UpperEntryPair n)) * K)) *
        (‖V (quotientRepresentative (t + 1) q')‖ *
          Real.exp ((d.exponent.re + s.re + ((t : ℝ) + 1) / 2) * ∑ j, alphaQ q' j) *
          ((1 + ‖lastRow (quotientRepresentative (t + 1) q')‖) ^ K₂)⁻¹) *
        (‖W (quotientRepresentative t q)‖ *
          Real.exp (-(d.exponent.re + ((t : ℝ) + 2) / 2) * ∑ i, alphaQ q i) *
          ∏ i : Fin m, ((1 + Real.exp (alphaQ q' i.castSucc - alphaQ q i)) ^ K)⁻¹) *
        ∏ p : UpperEntryPair n, ((1 + Real.exp (alphaQ q' p.1.2 - alphaQ q (pairRow p)) *
            |u.val.val p.1.1 p.1.2|) ^ K)⁻¹ := by
  rw [norm_kernel_chart d (Ψ : Y → ℂ) W V hVu s q' q u]
  have hsq : squareFirstRows ((pad (quotientRepresentative t q))⁻¹ *
      (u.val * quotientRepresentative (t + 1) q')).val =
      (torus (alphaQ q) * (kpart (quotientRepresentative t q) : G))⁻¹.val *
        squareFirstRows (u.val * (torus (alphaQ q') *
          (kpart (quotientRepresentative (t + 1) q') : H))).val := by
    rw [← map_inv pad, squareFirstRows_pad_mul', ← quotientRepresentative_eq_torus,
      ← quotientRepresentative_eq_torus]
  have hrow : lastRow ((pad (quotientRepresentative t q))⁻¹ *
      (u.val * quotientRepresentative (t + 1) q')) =
      lastRow (quotientRepresentative (t + 1) q') := by
    rw [← map_inv pad, lastRow_pad_mul', lastRow_unipotent_mul]
  have hA := inv_one_add_norm_pow_le K (alphaQ q) (kpart (quotientRepresentative t q))
    (alphaQ q') (kpart (quotientRepresentative (t + 1) q')) u
  rw [← hsq] at hA
  have hΨ := norm_schwartz_le_split Ψ ((m + Fintype.card (UpperEntryPair n)) * K) K₂
    ((pad (quotientRepresentative t q))⁻¹ * (u.val * quotientRepresentative (t + 1) q'))
  rw [hrow] at hΨ
  set S := (Finset.Iic ((m + Fintype.card (UpperEntryPair n)) * K + K₂, 0)).sup
    (fun r : ℕ × ℕ => SchwartzMap.seminorm ℝ r.1 r.2) Ψ with hS
  have hS0 : 0 ≤ S := apply_nonneg _ _
  set A₂ := ((1 + ‖lastRow (quotientRepresentative (t + 1) q')‖) ^ K₂)⁻¹ with hA₂
  have hA₂0 : 0 ≤ A₂ := by positivity
  have hΨ' : ‖Ψ ((pad (quotientRepresentative t q))⁻¹ *
      (u.val * quotientRepresentative (t + 1) q')).val‖ ≤
      2 ^ ((m + Fintype.card (UpperEntryPair n)) * K + K₂) * S *
        ((((m : ℝ) * n) ^ ((m + Fintype.card (UpperEntryPair n)) * K) *
          ((∏ i : Fin m, ((1 + Real.exp (alphaQ q' i.castSucc - alphaQ q i)) ^ K)⁻¹) *
            ∏ p : UpperEntryPair n, ((1 + Real.exp (alphaQ q' p.1.2 - alphaQ q (pairRow p)) *
              |u.val.val p.1.1 p.1.2|) ^ K)⁻¹)) * A₂) :=
    hΨ.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hA hA₂0)
      (mul_nonneg (by positivity) hS0))
  have hV0 : 0 ≤ ‖V (quotientRepresentative (t + 1) q')‖ *
      Real.exp ((d.exponent.re + s.re + ((t : ℝ) + 1) / 2) * ∑ j, alphaQ q' j) := by positivity
  have hW0 : 0 ≤ ‖W (quotientRepresentative t q)‖ *
      Real.exp (-(d.exponent.re + ((t : ℝ) + 2) / 2) * ∑ i, alphaQ q i) := by positivity
  calc
    _ ≤ (2 ^ ((m + Fintype.card (UpperEntryPair n)) * K + K₂) * S *
        ((((m : ℝ) * n) ^ ((m + Fintype.card (UpperEntryPair n)) * K) *
          ((∏ i : Fin m, ((1 + Real.exp (alphaQ q' i.castSucc - alphaQ q i)) ^ K)⁻¹) *
            ∏ p : UpperEntryPair n, ((1 + Real.exp (alphaQ q' p.1.2 - alphaQ q (pairRow p)) *
              |u.val.val p.1.1 p.1.2|) ^ K)⁻¹)) * A₂)) *
        (‖V (quotientRepresentative (t + 1) q')‖ *
          Real.exp ((d.exponent.re + s.re + ((t : ℝ) + 1) / 2) * ∑ j, alphaQ q' j)) *
        (‖W (quotientRepresentative t q)‖ *
          Real.exp (-(d.exponent.re + ((t : ℝ) + 2) / 2) * ∑ i, alphaQ q i)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hΨ' hV0) hW0
    _ = _ := by ring


/-! ### Integration over an arbitrary unipotent Haar measure -/

/-- Integration of the entrywise decay against any Haar measure on the larger upper
unipotent group: up to a finite constant, each entry contributes the inverse of its
scaling factor. -/
private theorem exists_lintegral_unipotent_decay (μU : Measure U) [μU.IsHaarMeasure] (K : ℕ)
    (hK : 2 ≤ K) : ∃ C₀ : ℝ≥0∞, C₀ < ⊤ ∧ ∀ l : UpperEntryPair n → ℝ,
      ∫⁻ u, ENNReal.ofReal (∏ p, ((1 + Real.exp (l p) * |u.val.val p.1.1 p.1.2|) ^ K)⁻¹) ∂μU =
        C₀ * ENNReal.ofReal (Real.exp (-∑ p, l p)) := by
  have := upperStepHaar_isHaar (t + 1) 1
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, μU = c • upperStepHaar (t + 1) 1 :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul μU (upperStepHaar (t + 1) 1)⟩
  set I : ℝ := ∫ v, ((1 + |v|) ^ K)⁻¹ ∂(realSelfDualMeasure (1 : ℝˣ)).measure with hI
  have hI0 : 0 ≤ I := integral_nonneg fun v => by positivity
  refine ⟨(c : ℝ≥0∞) * ENNReal.ofReal (I ^ Fintype.card (UpperEntryPair n)),
    ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top, fun l => ?_⟩
  have h := lintegral_upperStep_entry_decay (t + 1) 1 K hK l
  simp only [upperEntryCoordinates_apply] at h
  rw [hc, lintegral_smul_measure, h, ENNReal.smul_def, smul_eq_mul,
    ENNReal.ofReal_mul (pow_nonneg hI0 _), mul_assoc]

/-! ### Continuity -/

private theorem continuous_determinantWeight' {j : ℕ} (c : RealCharacterData) (z : ℂ) :
    Continuous (determinantWeight c z : Langlands.GeneralLinear j ℝ → ℂ) := by
  have hval : Continuous (fun g : Langlands.GeneralLinear j ℝ => g.val.det) :=
    Units.continuous_val.matrix_det
  have hDet : Continuous (determinant : Langlands.GeneralLinear j ℝ → ℝˣ) := by
    refine Units.continuous_iff.mpr ⟨hval, ?_⟩
    simp only [← map_inv]
    change Continuous (fun g : Langlands.GeneralLinear j ℝ => (g⁻¹).val.det)
    exact hval.comp continuous_inv
  have hbase : Continuous (fun g : Langlands.GeneralLinear j ℝ => ((|g.val.det| : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hval.abs
  have hpow : Continuous (fun g : Langlands.GeneralLinear j ℝ => ((|g.val.det| : ℝ) : ℂ) ^ z) := by
    refine continuous_iff_continuousAt.mpr fun g => ?_
    have h : ContinuousAt (fun x : ℂ => x ^ z) ((|g.val.det| : ℝ) : ℂ) :=
      continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr
        (abs_pos.mpr (determinant g).ne_zero))
    exact ContinuousAt.comp (f := fun k : Langlands.GeneralLinear j ℝ => ((|k.val.det| : ℝ) : ℂ))
      h (hbase.continuousAt (x := g))
  exact (Units.continuous_val.comp (c.character.continuous.comp hDet)).mul hpow

private theorem continuous_detPower' {j : ℕ} (z : ℂ) :
    Continuous (fun g : Langlands.GeneralLinear j ℝ => P g z) := by
  have hval : Continuous (fun g : Langlands.GeneralLinear j ℝ => g.val.det) :=
    Units.continuous_val.matrix_det
  have hbase : Continuous (fun g : Langlands.GeneralLinear j ℝ => ((|g.val.det| : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hval.abs
  have h : (fun g : Langlands.GeneralLinear j ℝ => P g z) =
      fun g => ((|g.val.det| : ℝ) : ℂ) ^ z := funext fun g => detPower_eq_cpow' g z
  rw [h]
  refine continuous_iff_continuousAt.mpr fun g => ?_
  have h' : ContinuousAt (fun x : ℂ => x ^ z) ((|g.val.det| : ℝ) : ℂ) :=
    continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr
      (abs_pos.mpr (determinant g).ne_zero))
  exact ContinuousAt.comp (f := fun k : Langlands.GeneralLinear j ℝ => ((|k.val.det| : ℝ) : ℂ))
    h' (hbase.continuousAt (x := g))

/-- The unfolded kernel is continuous on the product of the smaller quotient and the
larger group. -/
theorem continuous_equalUnfoldedKernel (d : RealCharacterData) (Ψ : 𝓢(Y, ℂ)) {W : G → ℂ}
    {V : H → ℂ} (hWc : Continuous W) (hVc : Continuous V) (s : ℂ) :
    Continuous (equalUnfoldedKernel d Ψ W V s) := by
  have hh : Continuous fun p : Q × H => quotientRepresentative t p.1 :=
    (continuous_representative' t).comp continuous_fst
  have h1 : Continuous fun p : Q × H => Ψ p.2.val :=
    Ψ.continuous.comp (Units.continuous_val.comp continuous_snd)
  have h2 : Continuous fun p : Q × H => V (pad (quotientRepresentative t p.1) * p.2) :=
    hVc.comp (((UnequalAnalytic.continuous_padGL _).comp hh).mul continuous_snd)
  have h3 : Continuous fun p : Q × H => determinantWeight d (s + (m : ℂ) / 2) p.2 :=
    (continuous_determinantWeight' d _).comp continuous_snd
  have h4 : Continuous fun p : Q × H => W (quotientRepresentative t p.1) := hWc.comp hh
  have h5 : Continuous fun p : Q × H => P (quotientRepresentative t p.1) (s - 1 / 2) :=
    (continuous_detPower' _).comp hh
  exact (((h1.mul h2).mul h3).mul h4).mul h5

private theorem continuous_lastRow' : Continuous (lastRow : H → Fin n → ℝ) :=
  continuous_pi fun j => (Langlands.GeneralLinear.entry (Fin.last m) j).continuous

/-! ### Decay along the last row of the larger representative -/

/-- Exponential growth in the last toral coordinate is absorbed by polynomial decay in
the last row. -/
private theorem exp_mul_inv_lastRow_le {c Ko : ℝ} {K₂ : ℕ} (hc : 0 ≤ c)
    (hK : c + Ko ≤ K₂) (y : Fin n → ℝ) (k : unitaryCompact ℝ n) :
    Real.exp (c * y (Fin.last m)) * ((1 + ‖lastRow (torus y * (k : H))‖) ^ K₂)⁻¹ ≤
      (((m : ℕ) : ℝ) + 1) ^ K₂ * Real.exp (-Ko * max (y (Fin.last m)) 0) := by
  set R := ‖lastRow (torus y * (k : H))‖ with hR
  set yl := y (Fin.last m) with hyl
  have hR0 : 0 ≤ R := norm_nonneg _
  have hB1 : (1 : ℝ) ≤ ((m : ℕ) : ℝ) + 1 := by
    have : (0 : ℝ) ≤ ((m : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hpos : 0 < (1 + R) ^ K₂ := by positivity
  rcases le_or_gt yl 0 with hy | hy
  · rw [max_eq_right hy, mul_zero, Real.exp_zero, mul_one]
    have h1 : Real.exp (c * yl) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have h2 : ((1 + R) ^ K₂)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
    calc
      Real.exp (c * yl) * ((1 + R) ^ K₂)⁻¹ ≤ 1 * 1 :=
        mul_le_mul h1 h2 (by positivity) zero_le_one
      _ = 1 := one_mul 1
      _ ≤ _ := one_le_pow₀ hB1
  · rw [max_eq_left hy.le, neg_mul, Real.exp_neg, ← div_eq_mul_inv, ← div_eq_mul_inv,
      div_le_div_iff₀ hpos (Real.exp_pos _)]
    have he := RealEqualConvergence.exp_le_mul_norm_lastRow y k
    rw [← hR, ← hyl] at he
    calc
      Real.exp (c * yl) * Real.exp (Ko * yl) = Real.exp ((c + Ko) * yl) := by
        rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp ((K₂ : ℝ) * yl) := Real.exp_le_exp.mpr (by nlinarith)
      _ = Real.exp yl ^ K₂ := by rw [← Real.exp_nat_mul]
      _ ≤ ((((m : ℕ) : ℝ) + 1) * (1 + R)) ^ K₂ := by
        gcongr
        nlinarith
      _ = (((m : ℕ) : ℝ) + 1) ^ K₂ * (1 + R) ^ K₂ := mul_pow _ _ _

private theorem neg_sum_pair_le (y : Fin n → ℝ) :
    -∑ p : UpperEntryPair n, y p.1.2 ≤ Fintype.card (UpperEntryPair n) * ∑ j, |y j| := by
  rw [← Finset.sum_neg_distrib]
  calc
    ∑ p : UpperEntryPair n, -y p.1.2 ≤ ∑ _p : UpperEntryPair n, ∑ j, |y j| :=
      Finset.sum_le_sum fun p _ => (neg_le_abs _).trans
        (Finset.single_le_sum (f := fun j => |y j|) (fun j _ => abs_nonneg _) (Finset.mem_univ _))
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]


/-! ### Integration over the smaller quotient and the unipotent variable -/

/-- For a fixed larger class, the integral over the smaller quotient and the larger
unipotent group of the pointwise majorant is bounded by a function of the toral
coordinate of the larger class. -/
private theorem lintegral_inner_le {ν : Measure Q} {κ : ℝ≥0} {L : (Fin m → ℝ) →L[ℝ] ℝ}
    (hκL : ∀ B : (Fin m → ℝ) → ℝ≥0∞, Measurable B →
      ∫⁻ q, B (alphaQ q) ∂ν = (κ : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (Real.exp (L x)) * B x)
    (μU : Measure U) [SFinite μU] {C₀ : ℝ≥0∞} (hC₀ : C₀ < ⊤) {K : ℕ}
    (hU : ∀ l : UpperEntryPair n → ℝ,
      ∫⁻ u, ENNReal.ofReal (∏ p, ((1 + Real.exp (l p) * |u.val.val p.1.1 p.1.2|) ^ K)⁻¹) ∂μU =
        C₀ * ENNReal.ofReal (Real.exp (-∑ p, l p)))
    (W : G → ℂ) {N CW : ℝ} (hCW : 0 ≤ CW) (hN : 0 ≤ N)
    (hW : ∀ (η : Fin m → ℝ) (k : unitaryCompact ℝ m),
      ‖W (torus η * (k : G))‖ ≤ CW * Real.exp (N * ∑ i, |η i|))
    {c : ℝ} (hc : ‖L‖ + N + Fintype.card (UpperEntryPair n) + 1 ≤ c)
    (hK : ‖L‖ + N + Fintype.card (UpperEntryPair n) + c + 1 ≤ K) (y : Fin n → ℝ)
    {A : ℝ} (hA : 0 ≤ A) (F : Q × U → ℝ≥0∞)
    (hF : ∀ q u, F (q, u) ≤ ENNReal.ofReal (A *
        (‖W (quotientRepresentative t q)‖ * Real.exp (-c * ∑ i, alphaQ q i) *
          ∏ i : Fin m, ((1 + Real.exp (y i.castSucc - alphaQ q i)) ^ K)⁻¹) *
        ∏ p : UpperEntryPair n, ((1 + Real.exp (y p.1.2 - alphaQ q (pairRow p)) *
            |u.val.val p.1.1 p.1.2|) ^ K)⁻¹)) :
    ∫⁻ x, F x ∂(ν.prod μU) ≤ ENNReal.ofReal A * (C₀ *
      (ENNReal.ofReal (Real.exp (-∑ p : UpperEntryPair n, y p.1.2)) *
        ((κ : ℝ≥0∞) * (ENNReal.ofReal (CW * Real.exp ((‖L‖ + N + Fintype.card (UpperEntryPair n)) *
            ∑ j, |y j| - c * ∑ i : Fin m, y i.castSucc)) *
          ∫⁻ x : Fin m → ℝ, ENNReal.ofReal (Real.exp (-1 * ∑ i, |x i|)))))) := by
  obtain ⟨w, hw⟩ : ∃ w : Q → ℝ, ∀ q, w q = ‖W (quotientRepresentative t q)‖ *
      Real.exp (-c * ∑ i, alphaQ q i) *
        ∏ i : Fin m, ((1 + Real.exp (y i.castSucc - alphaQ q i)) ^ K)⁻¹ := ⟨_, fun _ => rfl⟩
  have hw0 : ∀ q, 0 ≤ w q := fun q => by
    rw [hw]
    have : 0 ≤ ∏ i : Fin m, ((1 + Real.exp (y i.castSucc - alphaQ q i)) ^ K)⁻¹ :=
      Finset.prod_nonneg fun i _ => by positivity
    positivity
  have hsplit : ∀ q : Q, Real.exp (-∑ p : UpperEntryPair n, (y p.1.2 - alphaQ q (pairRow p))) =
      Real.exp (-∑ p : UpperEntryPair n, y p.1.2) *
        Real.exp (∑ p : UpperEntryPair n, alphaQ q (pairRow p)) := by
    intro q
    rw [← Real.exp_add, Finset.sum_sub_distrib]
    ring_nf
  have hconst : ENNReal.ofReal A * (C₀ * ENNReal.ofReal (Real.exp (-∑ p : UpperEntryPair n, y p.1.2)))
      ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hC₀.ne ENNReal.ofReal_ne_top)
  have hQ := lintegral_quotient_bound hκL W hCW hN hW hc hK y
  calc
    ∫⁻ x, F x ∂(ν.prod μU) ≤ ∫⁻ q, ∫⁻ u, F (q, u) ∂μU ∂ν := lintegral_prod_le F
    _ ≤ ∫⁻ q, ∫⁻ u, ENNReal.ofReal (A * w q) * ENNReal.ofReal (∏ p : UpperEntryPair n,
          ((1 + Real.exp (y p.1.2 - alphaQ q (pairRow p)) * |u.val.val p.1.1 p.1.2|) ^ K)⁻¹)
          ∂μU ∂ν := by
      refine lintegral_mono fun q => lintegral_mono fun u => (hF q u).trans_eq ?_
      rw [← hw, ENNReal.ofReal_mul (mul_nonneg hA (hw0 q))]
    _ = ∫⁻ q, ENNReal.ofReal (A * w q) * (C₀ * ENNReal.ofReal
          (Real.exp (-∑ p : UpperEntryPair n, (y p.1.2 - alphaQ q (pairRow p))))) ∂ν := by
      refine lintegral_congr fun q => ?_
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      congr 1
      exact hU (fun p => y p.1.2 - alphaQ q (pairRow p))
    _ = ∫⁻ q, (ENNReal.ofReal A * (C₀ * ENNReal.ofReal
          (Real.exp (-∑ p : UpperEntryPair n, y p.1.2)))) *
          ENNReal.ofReal (w q * Real.exp (∑ p : UpperEntryPair n, alphaQ q (pairRow p))) ∂ν := by
      refine lintegral_congr fun q => ?_
      rw [hsplit, ENNReal.ofReal_mul hA, ENNReal.ofReal_mul (Real.exp_pos _).le,
        ENNReal.ofReal_mul (hw0 q)]
      ring
    _ = (ENNReal.ofReal A * (C₀ * ENNReal.ofReal
          (Real.exp (-∑ p : UpperEntryPair n, y p.1.2)))) *
          ∫⁻ q, ENNReal.ofReal (w q * Real.exp (∑ p : UpperEntryPair n, alphaQ q (pairRow p))) ∂ν :=
      lintegral_const_mul' _ _ hconst
    _ ≤ (ENNReal.ofReal A * (C₀ * ENNReal.ofReal
          (Real.exp (-∑ p : UpperEntryPair n, y p.1.2)))) *
          ((κ : ℝ≥0∞) * (ENNReal.ofReal (CW * Real.exp ((‖L‖ + N + Fintype.card (UpperEntryPair n)) *
            ∑ j, |y j| - c * ∑ i : Fin m, y i.castSucc)) *
          ∫⁻ x : Fin m → ℝ, ENNReal.ofReal (Real.exp (-1 * ∑ i, |x i|)))) := by
      gcongr
      simp_rw [hw]
      exact hQ
    _ = _ := by ring

/-! ### Joint absolute convergence -/

variable (t) in
/-- The convergence abscissas of the unfolded equal-rank kernel can be chosen from the two
fixed toral growth exponents and the two quotient data. The constants and Schwartz seminorm
in the bound can depend on the functions and the real parts of the two parameters. -/
def RealLocalEqualUniformJointIntegrabilityStatement : Prop :=
  ∀ (D : RealQuotientMeasureData t) (D' : RealQuotientMeasureData (t + 1)) (NW NV : ℕ),
    ∃ ρ σ : ℝ, ∀ (W : G → ℂ) (V : H → ℂ), Continuous W → Continuous V →
      (∃ C : ℝ, 0 ≤ C ∧ ∀ (y : Fin m → ℝ) (k : unitaryCompact ℝ m),
        ‖W (torus y * (k : G))‖ ≤ C * Real.exp ((NW : ℝ) * ∑ i, |y i|)) →
      (∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : Fin n → ℝ) (k : unitaryCompact ℝ n),
        ‖V (torus y * (k : H))‖ ≤
          C * Real.exp (-(M : ℝ) * rootPos y + (NV : ℝ) * ∑ i, |y i|)) →
      (∀ (u : U) (g : H), ‖V (u.val * g)‖ = ‖V g‖) →
      ∀ x₀ y₀ : ℝ, ρ ≤ x₀ → σ < y₀ → ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧
        ∀ (Ψ : 𝓢(Y, ℂ)) (d : RealCharacterData) (s : ℂ), d.exponent.re = x₀ → s.re = y₀ →
          Integrable (equalUnfoldedKernel d Ψ W V s) (D.measure.prod D'.groupHaar) ∧
          ∫ p, ‖equalUnfoldedKernel d Ψ W V s p‖ ∂(D.measure.prod D'.groupHaar) ≤
            C * (Finset.Iic (k, 0)).sup (fun r : ℕ × ℕ => SchwartzMap.seminorm ℝ r.1 r.2) Ψ

set_option maxHeartbeats 1800000 in
theorem realLocalEqualUniformJointIntegrability : RealLocalEqualUniformJointIntegrabilityStatement t := by
  intro D D' NW NV
  let := D.unipotentHaar_rightInvariant
  let := D'.unipotentHaar_rightInvariant
  let := D.groupHaar_isHaar
  let := D'.groupHaar_isHaar
  let := D.unipotentHaar_isHaar
  let := D'.unipotentHaar_isHaar
  let := D.compatible.regular
  let := D'.compatible.regular
  obtain ⟨κ, L, hκL⟩ := exists_lintegral_alphaQ D.groupHaar D.unipotentHaar D.measure D.compatible
  obtain ⟨κ', L', hκL'⟩ :=
    exists_lintegral_alphaQ D'.groupHaar D'.unipotentHaar D'.measure D'.compatible
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = ‖L‖ + NW + Fintype.card (UpperEntryPair n) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = NV + α + Fintype.card (UpperEntryPair n) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = (A + ‖L'‖ + 1) * (((t + 1 : ℕ) : ℝ) + 1) := ⟨_, rfl⟩
  have hcard0 : (0 : ℝ) ≤ Fintype.card (UpperEntryPair n) := Nat.cast_nonneg _
  have hNW0 : (0 : ℝ) ≤ NW := Nat.cast_nonneg _
  have hNV0 : (0 : ℝ) ≤ NV := Nat.cast_nonneg _
  have hL0 : 0 ≤ ‖L‖ := norm_nonneg _
  have hα0 : 0 ≤ α := by rw [hα]; linarith
  have hA0 : 0 ≤ A := by rw [hA]; linarith
  refine ⟨α + 1 - ((t : ℝ) + 2) / 2, B + 1 / 2, ?_⟩
  intro W V hWc hVc hWg hNV hVu x₀ y₀ hx₀ hy₀
  obtain ⟨CW, hCW, hW⟩ := hWg
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = x₀ + ((t : ℝ) + 2) / 2 := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = y₀ - 1 / 2 := ⟨_, rfl⟩
  have hcα : α + 1 ≤ c := by rw [hc]; linarith
  have hc0 : 0 ≤ c := by linarith
  have hτB : B ≤ τ := by rw [hτ]; linarith
  obtain ⟨Mo, hMo⟩ : ∃ Mo : ℕ, Mo = ⌈B + τ * (((t + 1 : ℕ) : ℝ) + 1)⌉₊ := ⟨_, rfl⟩
  have hMoB : B + τ * (((t + 1 : ℕ) : ℝ) + 1) ≤ (Mo : ℝ) := by rw [hMo]; exact Nat.le_ceil _
  obtain ⟨CV, hCV, hV⟩ := hNV Mo
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ, K = max 2 ⌈α + c + 1⌉₊ := ⟨_, rfl⟩
  have hK2 : 2 ≤ K := by rw [hKdef]; exact le_max_left _ _
  have hKc : α + c + 1 ≤ (K : ℝ) := by
    rw [hKdef]
    exact (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
  obtain ⟨K₂, hK₂def⟩ : ∃ K₂ : ℕ, K₂ = ⌈c + (Mo : ℝ)⌉₊ := ⟨_, rfl⟩
  have hK₂ : c + (Mo : ℝ) ≤ (K₂ : ℝ) := by rw [hK₂def]; exact Nat.le_ceil _
  obtain ⟨C₀, hC₀, hU⟩ := exists_lintegral_unipotent_decay D'.unipotentHaar K hK2
  -- The majorant on the larger quotient.
  obtain ⟨Vp, hVp⟩ : ∃ Vp : Q' → ℝ, ∀ q', Vp q' = ‖V (quotientRepresentative (t + 1) q')‖ *
      Real.exp ((x₀ + y₀ + ((t : ℝ) + 1) / 2) * ∑ j, alphaQ q' j) *
      ((1 + ‖lastRow (quotientRepresentative (t + 1) q')‖) ^ K₂)⁻¹ := ⟨_, fun _ => rfl⟩
  have hVp0 : ∀ q', 0 ≤ Vp q' := fun q' => by rw [hVp]; positivity
  obtain ⟨Fo, hFo⟩ : ∃ Fo : Q' → ℝ, ∀ q', Fo q' = Vp q' *
      Real.exp (-∑ p : UpperEntryPair n, alphaQ q' p.1.2) *
      (CW * Real.exp (α * ∑ j, |alphaQ q' j| - c * ∑ i : Fin m, alphaQ q' i.castSucc)) :=
    ⟨_, fun _ => rfl⟩
  have hFo0 : ∀ q', 0 ≤ Fo q' := fun q' => by
    rw [hFo]
    exact mul_nonneg (mul_nonneg (hVp0 q') (Real.exp_pos _).le)
      (mul_nonneg hCW (Real.exp_pos _).le)
  have hrep := continuous_representative' (t + 1)
  have hyc : Continuous (fun q' : Q' => alphaQ q') := continuous_alphaQ
  have hVpc : Continuous Vp := by
    rw [funext hVp]
    have h1 : Continuous fun q' : Q' => ‖V (quotientRepresentative (t + 1) q')‖ :=
      (hVc.comp hrep).norm
    have h2 : Continuous fun q' : Q' => ∑ j, alphaQ q' j :=
      continuous_finsetSum _ fun j _ => (continuous_apply j).comp hyc
    have h3 : Continuous fun q' : Q' =>
        ((1 + ‖lastRow (quotientRepresentative (t + 1) q')‖) ^ K₂)⁻¹ :=
      ((continuous_const.add (continuous_lastRow'.comp hrep).norm).pow K₂).inv₀
        fun q' => (pow_pos (by positivity :
          (0 : ℝ) < 1 + ‖lastRow (quotientRepresentative (t + 1) q')‖) K₂).ne'
    exact (h1.mul (Real.continuous_exp.comp (continuous_const.mul h2))).mul h3
  have hFoc : Continuous Fo := by
    rw [funext hFo]
    have h4 : Continuous fun q' : Q' => ∑ p : UpperEntryPair n, alphaQ q' p.1.2 :=
      continuous_finsetSum _ fun p _ => (continuous_apply _).comp hyc
    have h5 : Continuous fun q' : Q' => ∑ j, |alphaQ q' j| :=
      continuous_finsetSum _ fun j _ => ((continuous_apply j).comp hyc).abs
    have h6 : Continuous fun q' : Q' => ∑ i : Fin m, alphaQ q' i.castSucc :=
      continuous_finsetSum _ fun i _ => (continuous_apply _).comp hyc
    exact (hVpc.mul (Real.continuous_exp.comp h4.neg)).mul (continuous_const.mul
      (Real.continuous_exp.comp ((continuous_const.mul h5).sub (continuous_const.mul h6))))
  -- Integrability of the majorant on the larger quotient.
  have hFoi : Integrable Fo D'.measure := by
    refine RealEqualConvergence.integrable_of_toral_bound
      (C := CV * CW * (((m : ℕ) : ℝ) + 1) ^ K₂) (A := A) (t := τ) (M := (Mo : ℝ))
      (K := (Mo : ℝ)) hκL' hFoc.aestronglyMeasurable
      (mul_nonneg (mul_nonneg hCV hCW) (by positivity)) hA0 (hB.symm.trans_le hτB)
      (by rw [hB] at hMoB; exact hMoB) (by rw [hB] at hMoB; exact hMoB) fun q' => ?_
    have hVb := hV (alphaQ q') (kpart (quotientRepresentative (t + 1) q'))
    have hlast := exp_mul_inv_lastRow_le (c := c) (Ko := (Mo : ℝ)) hc0 hK₂ (alphaQ q')
      (kpart (quotientRepresentative (t + 1) q'))
    have hpair := neg_sum_pair_le (alphaQ q')
    have hsum : ∑ j, alphaQ q' j = ∑ i : Fin m, alphaQ q' i.castSucc + alphaQ q' (Fin.last m) :=
      Fin.sum_univ_castSucc _
    rw [Real.norm_of_nonneg (hFo0 q'), hFo, hVp, quotientRepresentative_eq_torus (t + 1) q']
    generalize kpart (quotientRepresentative (t + 1) q') = k at hVb hlast ⊢
    generalize alphaQ q' = y at hVb hlast hpair hsum ⊢
    have hkey : Real.exp ((x₀ + y₀ + ((t : ℝ) + 1) / 2) * ∑ j, y j) *
        Real.exp (-∑ p : UpperEntryPair n, y p.1.2) *
        Real.exp (α * ∑ j, |y j| - c * ∑ i : Fin m, y i.castSucc) =
        Real.exp (c * y (Fin.last m)) *
          Real.exp (τ * ∑ j, y j + α * ∑ j, |y j| + -∑ p : UpperEntryPair n, y p.1.2) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      rw [hsum, hc, hτ]
      ring
    have hexp : Real.exp (τ * ∑ j, y j + α * ∑ j, |y j| + -∑ p : UpperEntryPair n, y p.1.2) ≤
        Real.exp (τ * ∑ j, y j + (α + Fintype.card (UpperEntryPair n)) * ∑ j, |y j|) :=
      Real.exp_le_exp.mpr (by linarith)
    have hfin : Real.exp (-(Mo : ℝ) * rootPos y + A * ∑ j, |y j| + τ * ∑ j, y j -
        (Mo : ℝ) * max (y (Fin.last m)) 0) =
        Real.exp (-(Mo : ℝ) * rootPos y + (NV : ℝ) * ∑ j, |y j|) *
          Real.exp (-(Mo : ℝ) * max (y (Fin.last m)) 0) *
          Real.exp (τ * ∑ j, y j + (α + Fintype.card (UpperEntryPair n)) * ∑ j, |y j|) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      rw [hA]
      ring
    set Vn := ‖V (torus y * (k : H))‖ with hVn
    set Rl := ((1 + ‖lastRow (torus y * (k : H))‖) ^ K₂)⁻¹ with hRl
    have hRl0 : 0 ≤ Rl := by rw [hRl]; positivity
    calc
      _ = Vn * (Real.exp (c * y (Fin.last m)) * Rl) *
          (CW * Real.exp (τ * ∑ j, y j + α * ∑ j, |y j| + -∑ p : UpperEntryPair n, y p.1.2)) := by
        linear_combination (Vn * Rl * CW) * hkey
      _ ≤ (CV * Real.exp (-(Mo : ℝ) * rootPos y + (NV : ℝ) * ∑ j, |y j|)) *
          ((((m : ℕ) : ℝ) + 1) ^ K₂ * Real.exp (-(Mo : ℝ) * max (y (Fin.last m)) 0)) *
          (CW * Real.exp (τ * ∑ j, y j + (α + Fintype.card (UpperEntryPair n)) * ∑ j, |y j|)) :=
        mul_le_mul (mul_le_mul hVb hlast (by positivity) (mul_nonneg hCV (Real.exp_pos _).le))
          (mul_le_mul_of_nonneg_left hexp hCW) (mul_nonneg hCW (Real.exp_pos _).le)
          (mul_nonneg (mul_nonneg hCV (Real.exp_pos _).le) (by positivity))
      _ = _ := by
        rw [hfin]
        ring
  have hIo : ∫⁻ q', ENNReal.ofReal (Fo q') ∂D'.measure < ⊤ := hFoi.lintegral_lt_top
  -- The constants.
  set Z := ∫⁻ x : Fin m → ℝ, ENNReal.ofReal (Real.exp (-1 * ∑ i, |x i|)) with hZ
  have hZ' : Z < ⊤ := lintegral_exp_neg_mul_sum_abs_lt_top one_pos
  set C₁ : ℝ := 2 ^ ((m + Fintype.card (UpperEntryPair n)) * K + K₂) *
    ((m : ℝ) * n) ^ ((m + Fintype.card (UpperEntryPair n)) * K) with hC₁
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  set R0 : ℝ≥0∞ := ENNReal.ofReal C₁ * (C₀ * ((κ : ℝ≥0∞) * Z)) *
    ∫⁻ q', ENNReal.ofReal (Fo q') ∂D'.measure with hR0def
  have hR0 : R0 < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top hC₀ (ENNReal.mul_lt_top ENNReal.coe_lt_top hZ'))) hIo
  have hid : ∀ a b v e g : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ v → 0 ≤ e →
      ENNReal.ofReal (a * b * v) * (C₀ * (ENNReal.ofReal e * ((κ : ℝ≥0∞) *
        (ENNReal.ofReal g * Z)))) =
      ENNReal.ofReal a * (ENNReal.ofReal b * (C₀ * ((κ : ℝ≥0∞) * Z))) *
        ENNReal.ofReal (v * e * g) := by
    intro a b v e g ha hb hv he
    rw [ENNReal.ofReal_mul (mul_nonneg ha hb), ENNReal.ofReal_mul ha,
      ENNReal.ofReal_mul (mul_nonneg hv he), ENNReal.ofReal_mul hv]
    ring
  refine ⟨(m + Fintype.card (UpperEntryPair n)) * K + K₂, R0.toReal, ENNReal.toReal_nonneg,
    fun Ψ d s hd hs => ?_⟩
  set S := (Finset.Iic ((m + Fintype.card (UpperEntryPair n)) * K + K₂, 0)).sup
    (fun r : ℕ × ℕ => SchwartzMap.seminorm ℝ r.1 r.2) Ψ with hS
  have hS0 : 0 ≤ S := apply_nonneg _ _
  set J := equalUnfoldedKernel d Ψ W V s with hJ
  have hJc : Continuous J := continuous_equalUnfoldedKernel d Ψ hWc hVc s
  have he := measurePreserving_equalUnfoldingChart D D'
  have hbound : ∫⁻ p, ENNReal.ofReal ‖J p‖ ∂(D.measure.prod D'.groupHaar) ≤
      ENNReal.ofReal S * R0 := by
    calc
      ∫⁻ p, ENNReal.ofReal ‖J p‖ ∂(D.measure.prod D'.groupHaar)
          = ∫⁻ x, ENNReal.ofReal ‖J (equalUnfoldingChart t x)‖
              ∂(D'.measure.prod (D.measure.prod D'.unipotentHaar)) :=
        (he.lintegral_comp_emb (equalUnfoldingChart t).measurableEmbedding
          (fun p => ENNReal.ofReal ‖J p‖)).symm
      _ ≤ ∫⁻ q', ∫⁻ qu, ENNReal.ofReal ‖J (equalUnfoldingChart t (q', qu))‖
              ∂(D.measure.prod D'.unipotentHaar) ∂D'.measure := lintegral_prod_le _
      _ ≤ ∫⁻ q', ENNReal.ofReal (S * C₁ * Vp q') * (C₀ *
            (ENNReal.ofReal (Real.exp (-∑ p : UpperEntryPair n, alphaQ q' p.1.2)) *
              ((κ : ℝ≥0∞) * (ENNReal.ofReal (CW * Real.exp (α * ∑ j, |alphaQ q' j| -
                c * ∑ i : Fin m, alphaQ q' i.castSucc)) * Z)))) ∂D'.measure := by
        refine lintegral_mono fun q' => ?_
        refine (lintegral_inner_le hκL D'.unipotentHaar hC₀ hU W hCW hNW0 hW (c := c)
          (by linarith) (by linarith) (alphaQ q')
          (mul_nonneg (mul_nonneg hS0 hC₁0) (hVp0 q')) _ fun q u => ?_).trans_eq ?_
        · refine ENNReal.ofReal_le_ofReal ?_
          rw [hVp]
          have h := norm_kernel_chart_le d Ψ W V hVu s K K₂ q' q u
          rw [hd, hs, ← hc] at h
          exact h
        · rw [hα]
      _ = ∫⁻ q', (ENNReal.ofReal S * (ENNReal.ofReal C₁ * (C₀ * ((κ : ℝ≥0∞) * Z)))) *
            ENNReal.ofReal (Fo q') ∂D'.measure := by
        refine lintegral_congr fun q' => ?_
        rw [hFo]
        exact hid _ _ _ _ _ hS0 hC₁0 (hVp0 q') (Real.exp_pos _).le
      _ = (ENNReal.ofReal S * (ENNReal.ofReal C₁ * (C₀ * ((κ : ℝ≥0∞) * Z)))) *
            ∫⁻ q', ENNReal.ofReal (Fo q') ∂D'.measure :=
        lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hC₀.ne
            (ENNReal.mul_ne_top ENNReal.coe_ne_top hZ'.ne))))
      _ = ENNReal.ofReal S * R0 := by rw [hR0def, mul_assoc]
  have hfin : ENNReal.ofReal S * R0 < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hR0
  refine ⟨⟨hJc.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_norm]
    exact hbound.trans_lt hfin
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      hJc.norm.aestronglyMeasurable]
    calc
      (∫⁻ p, ENNReal.ofReal ‖J p‖ ∂(D.measure.prod D'.groupHaar)).toReal ≤
          (ENNReal.ofReal S * R0).toReal := ENNReal.toReal_mono hfin.ne hbound
      _ = R0.toReal * S := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hS0, mul_comm]


/-- **Joint absolute convergence of the unfolded kernel.** Let `W` and `V` be
continuous functions on `GL_(t+1)(ℝ)` and `GL_(t+2)(ℝ)` with gauge estimates, the
size of `V` invariant under left upper unipotent translation. There are thresholds
`ρ` for the real part of the separated character and `σ` for the real part of `s`
such that, for real parts `x₀ ≥ ρ` and `y₀ > σ`, the unfolded kernel is integrable
for every square Schwartz test, and its absolute integral is bounded by a fixed
constant times one Schwartz seminorm of the test. Only the order of the seminorm and
the constant depend on `x₀` and `y₀`; `σ` does not depend on `x₀`. -/
theorem exists_equalUnfoldedKernel_bound (D : RealQuotientMeasureData t)
    (D' : RealQuotientMeasureData (t + 1)) {W : G → ℂ} {V : H → ℂ}
    (hWc : Continuous W) (hVc : Continuous V)
    (hWg : RealEqualConvergence.HasGauge W) (hVg : RealEqualConvergence.HasGauge V)
    (hVu : ∀ (u : U) (g : H), ‖V (u.val * g)‖ = ‖V g‖) :
    ∃ ρ σ : ℝ, ∀ x₀ y₀ : ℝ, ρ ≤ x₀ → σ < y₀ → ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (Ψ : 𝓢(Y, ℂ)) (d : RealCharacterData) (s : ℂ), d.exponent.re = x₀ → s.re = y₀ →
        Integrable (equalUnfoldedKernel d Ψ W V s) (D.measure.prod D'.groupHaar) ∧
        ∫ p, ‖equalUnfoldedKernel d Ψ W V s p‖ ∂(D.measure.prod D'.groupHaar) ≤
          C * (Finset.Iic (k, 0)).sup (fun r : ℕ × ℕ => SchwartzMap.seminorm ℝ r.1 r.2) Ψ := by
  obtain ⟨NW, hNW⟩ := hWg
  obtain ⟨CW, hCW, hW₀⟩ := hNW 0
  have hW : ∀ (η : Fin m → ℝ) (k : unitaryCompact ℝ m),
      ‖W (torus η * (k : G))‖ ≤ CW * Real.exp ((NW : ℝ) * ∑ i, |η i|) := by
    intro η k
    have h := hW₀ η k
    rwa [Nat.cast_zero, neg_zero, zero_mul, zero_add] at h
  obtain ⟨NV, hNV⟩ := hVg
  obtain ⟨ρ, σ, h⟩ := realLocalEqualUniformJointIntegrability (t := t) D D' NW NV
  exact ⟨ρ, σ, h W V hWc hVc ⟨CW, hCW, hW⟩ hNV hVu⟩

variable (t) in
/-- Joint absolute convergence of the unfolded kernel of (8.1) for dominant exponents:
for continuous `W`, `V` with gauge estimates, the size of `V` invariant under left
upper unipotent translation, there are thresholds `ρ` for the real part of the
separated character and `σ` for the real part of `s` (not depending on the former)
above which the unfolded kernel is integrable for every square Schwartz test, with
absolute integral bounded by a constant times one Schwartz seminorm of the test. -/
def RealLocalEqualJointIntegrabilityStatement : Prop :=
  ∀ (D : RealQuotientMeasureData t) (D' : RealQuotientMeasureData (t + 1)) (W : G → ℂ)
    (V : H → ℂ), Continuous W → Continuous V → RealEqualConvergence.HasGauge W →
    RealEqualConvergence.HasGauge V → (∀ (u : U) (g : H), ‖V (u.val * g)‖ = ‖V g‖) →
    ∃ ρ σ : ℝ, ∀ x₀ y₀ : ℝ, ρ ≤ x₀ → σ < y₀ → ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (Ψ : 𝓢(Y, ℂ)) (d : RealCharacterData) (s : ℂ), d.exponent.re = x₀ → s.re = y₀ →
        Integrable (equalUnfoldedKernel d Ψ W V s) (D.measure.prod D'.groupHaar) ∧
        ∫ p, ‖equalUnfoldedKernel d Ψ W V s p‖ ∂(D.measure.prod D'.groupHaar) ≤
          C * (Finset.Iic (k, 0)).sup (fun r : ℕ × ℕ => SchwartzMap.seminorm ℝ r.1 r.2) Ψ

theorem realLocalEqualJointIntegrability : RealLocalEqualJointIntegrabilityStatement t :=
  fun D D' _ _ hWc hVc hWg hVg hVu => exists_equalUnfoldedKernel_bound D D' hWc hVc hWg hVg hVu

end Langlands.Global.RankinSelbergGlobal.RealGodement
