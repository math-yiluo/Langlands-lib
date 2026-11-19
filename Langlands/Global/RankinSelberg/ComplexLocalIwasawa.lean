import Langlands.Global.RankinSelberg.ComplexLocalWhittakerGauge
import Langlands.Representation.Archimedean.ComplexGramFormula
import Langlands.Representation.Archimedean.ComplexJacquetTorus
import Langlands.Representation.Archimedean.PrincipalSeriesAdmissible
import Langlands.Representation.RankinSelberg.DiagonalUnipotentHaar

/-! # Logarithmic Iwasawa coordinates on the complex matrix group -/

noncomputable section
open scoped Classical Matrix.Norms.Operator
open Langlands.Archimedean Langlands.GeneralLinear
open Langlands.QuotientIntegration (LeftQuotient descend)
open Complex
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexLocalIwasawa

open ComplexLocalWhittakerGauge (logTorus logTorus_val logTorus_inv_val)

variable {n : ℕ}

local notation "G" => Langlands.GeneralLinear n ℂ
local notation "N" => Langlands.GeneralLinear.upperUnipotent n ℂ
local notation "K" => unitaryCompact ℂ n
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

theorem logTorus_add (y z : Fin n → ℝ) : logTorus (y + z) = logTorus y * logTorus z := by
  apply Units.ext
  rw [Units.val_mul, logTorus_val, logTorus_val, logTorus_val, Matrix.diagonal_mul_diagonal]
  simp only [Pi.add_apply, Real.exp_add, Complex.ofReal_mul]

theorem logTorus_neg (y : Fin n → ℝ) : logTorus (-y) = (logTorus y)⁻¹ :=
  Units.ext (logTorus_inv_val y).symm

theorem continuous_logTorus : Continuous (logTorus (n := n)) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous (fun y : Fin n → ℝ => Matrix.diagonal fun i => (Real.exp (y i) : ℂ))
    exact Continuous.matrix_diagonal (continuous_pi fun j =>
      Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_apply j)))
  · change Continuous (fun y : Fin n → ℝ => (logTorus y)⁻¹.val)
    simp only [logTorus_inv_val]
    exact Continuous.matrix_diagonal (continuous_pi fun j =>
      Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_apply j).neg))

/-! ### Positive triangular matrices -/

private def PositiveUpper (b : Mat) : Prop :=
  b.IsUpperTriangular ∧ ∀ i, 0 < (b i i).re ∧ (b i i).im = 0

private theorem diag_mul_eq {b c : Mat} (hb : b.IsUpperTriangular) (hc : c.IsUpperTriangular)
    (i : Fin n) : (b * c) i i = b i i * c i i := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single i]
  intro j hj
  rcases lt_or_gt_of_ne hj with hj | hj
  · rw [hb hj, zero_mul]
  · rw [hc hj, mul_zero]

private theorem diag_eq_real {b : Mat} (hb : PositiveUpper b) (i : Fin n) :
    b i i = ((b i i).re : ℂ) :=
  Complex.ext (by simp) (by simpa using (hb.2 i).2)

private theorem PositiveUpper.mul {b c : Mat} (hb : PositiveUpper b) (hc : PositiveUpper c) :
    PositiveUpper (b * c) := by
  refine ⟨hb.1.mul hc.1, fun i => ?_⟩
  rw [diag_mul_eq hb.1 hc.1, diag_eq_real hb i, diag_eq_real hc i, ← Complex.ofReal_mul]
  exact ⟨mul_pos (hb.2 i).1 (hc.2 i).1, Complex.ofReal_im _⟩

private theorem PositiveUpper.inv {g : G} (hg : PositiveUpper g.val) :
    PositiveUpper g⁻¹.val := by
  let := g.invertible
  have htri : g⁻¹.val.IsUpperTriangular := by
    simpa only [Matrix.GeneralLinearGroup.coe_inv] using
      Matrix.blockTriangular_inv_of_blockTriangular hg.1
  refine ⟨htri, fun i => ?_⟩
  have h := congrArg (fun b : Mat => b i i) g.mul_inv
  change (g.val * g⁻¹.val) i i = (1 : Mat) i i at h
  rw [diag_mul_eq hg.1 htri, Matrix.one_apply_eq] at h
  have hinv := inv_eq_of_mul_eq_one_right h
  rw [← hinv, diag_eq_real hg i, ← Complex.ofReal_inv]
  exact ⟨inv_pos.mpr (hg.2 i).1, Complex.ofReal_im _⟩

private theorem logTorus_positiveUpper (y : Fin n → ℝ) : PositiveUpper (logTorus y).val := by
  rw [logTorus_val]
  refine ⟨Matrix.blockTriangular_diagonal _, fun i => ?_⟩
  rw [Matrix.diagonal_apply_eq]
  exact ⟨Real.exp_pos _, Complex.ofReal_im _⟩

private theorem unipotent_positiveUpper (u : N) : PositiveUpper u.val.val := by
  refine ⟨u.2.1, fun i => ?_⟩
  rw [GeneralLinear.UpperUnipotent.entry_diag u i]
  simp

private theorem eq_one_of_positiveUpper {g : G} (hg : PositiveUpper g.val)
    (hk : g ∈ K) : g = 1 := by
  have hU : g.val ∈ Matrix.unitaryGroup (Fin n) ℂ := hk
  have hoff := offDiag_eq_zero_of_upper_unitary hU hg.1
  have hdiag (i : Fin n) : g.val i i = 1 := by
    have h := congrArg (fun b : Mat => b i i) ((Matrix.mem_unitaryGroup_iff.mp hU))
    simp only [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply_eq] at h
    rw [Fintype.sum_eq_single i (fun j hj => by rw [hoff i j hj.symm, zero_mul])] at h
    rw [Complex.star_def, ComplexGramFormula.self_mul_conj_eq] at h
    have hsq : ‖g.val i i‖ ^ 2 = (1 : ℝ) := by exact_mod_cast h
    rw [diag_eq_real hg i, Complex.norm_real, Real.norm_of_nonneg (hg.2 i).1.le, sq] at hsq
    have hre : (g.val i i).re = 1 := by
      rcases mul_self_eq_one_iff.mp hsq with he | he
      · exact he
      · linarith [(hg.2 i).1]
    rw [diag_eq_real hg i, hre, Complex.ofReal_one]
  apply Units.ext
  ext i j
  by_cases hij : i = j
  · subst j
    exact (hdiag i).trans (Matrix.one_apply_eq i).symm
  · exact (hoff i j hij).trans (Matrix.one_apply_ne hij).symm

/-! ### Factorization and its unitary coordinate -/

/-- A complex invertible matrix is upper unipotent times positive diagonal times unitary. -/
theorem exists_iwasawa (g : G) :
    ∃ (u : N) (y : Fin n → ℝ) (k : K), g = (u : G) * logTorus y * (k : G) := by
  obtain ⟨d, u, k, hk, hg⟩ := PrincipalSeries.exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact g
  let y : Fin n → ℝ := fun i => Real.log ‖(d i : ℂ)‖
  let phase : G := Iwasawa.diagonalUnits (fun i => ComplexGramFormula.phaseUnit (d i))
  let v := Langlands.RankinSelberg.diagonalConj d u
  have hphase : phase ∈ K := ComplexGramFormula.diagonalUnits_phaseUnit_mem d
  have hD : Iwasawa.diagonalUnits d = logTorus y * phase := by
    apply Units.ext
    change Matrix.diagonal (fun i => (d i : ℂ)) =
      (logTorus y).val * Matrix.diagonal (fun i => (ComplexGramFormula.phaseUnit (d i) : ℂ))
    rw [logTorus_val, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    change (d i : ℂ) =
      (Real.exp (Real.log ‖(d i : ℂ)‖) : ℂ) * (ComplexGramFormula.phaseUnit (d i) : ℂ)
    rw [ComplexGramFormula.phaseUnit_val, Real.exp_log (norm_pos_iff.mpr (d i).ne_zero)]
    field_simp [Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (d i).ne_zero)]
  refine ⟨v, y, ⟨phase * k, mul_mem hphase hk⟩, ?_⟩
  change g = (v : G) * logTorus y * (phase * k)
  calc
    g = Iwasawa.diagonalUnits d * (u : G) * k := hg
    _ = (v : G) * Iwasawa.diagonalUnits d * k := by
      change _ = (Langlands.RankinSelberg.diagonalConj d u : G) * Iwasawa.diagonalUnits d * k
      rw [Langlands.RankinSelberg.diagonalConj_val, inv_mul_cancel_right]
    _ = _ := by rw [hD]; simp only [mul_assoc]

private theorem exists_kpart (g : G) : ∃ k : K, PositiveUpper (g * (k : G)⁻¹).val := by
  obtain ⟨u, y, k, rfl⟩ := exists_iwasawa g
  refine ⟨k, ?_⟩
  rw [mul_inv_cancel_right, Units.val_mul]
  exact (unipotent_positiveUpper u).mul (logTorus_positiveUpper y)

/-- The unique unitary component of the positive-diagonal Iwasawa decomposition. -/
def kpart (g : G) : K :=
  (exists_kpart g).choose

private theorem positiveUpper_bpart (g : G) : PositiveUpper (g * (kpart g : G)⁻¹).val :=
  (exists_kpart g).choose_spec

private theorem kpart_eq {g : G} {k : K} (hk : PositiveUpper (g * (k : G)⁻¹).val) :
    kpart g = k := by
  let c : G := (g * (k : G)⁻¹)⁻¹ * (g * (kpart g : G)⁻¹)
  have hc : c = (k : G) * (kpart g : G)⁻¹ := by dsimp only [c]; group
  have hc₁ : PositiveUpper c.val := hk.inv.mul (positiveUpper_bpart g)
  have hc₂ : c ∈ K := hc ▸ mul_mem k.2 (inv_mem (kpart g).2)
  have he := eq_one_of_positiveUpper hc₁ hc₂
  rw [hc, mul_inv_eq_one] at he
  exact Subtype.ext he.symm

theorem continuous_kpart : Continuous (kpart (n := n)) := by
  let b : G × K → Mat := fun p => (p.1 * (p.2 : G)⁻¹).val
  have hb : Continuous b :=
    Units.continuous_val.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd).inv)
  have hc (i : Fin n) : Continuous (fun p => b p i i) := (continuous_apply_apply i i).comp hb
  have hEq : Function.graph (kpart (n := n)) =
      {p | (b p).IsUpperTriangular} ∩
        ⋂ i : Fin n, {p | 0 ≤ (b p i i).re} ∩ {p | (b p i i).im = 0} := by
    ext ⟨g, k⟩
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    change kpart g = k ↔ _
    constructor
    · rintro rfl
      exact ⟨(positiveUpper_bpart g).1, fun i =>
        ⟨((positiveUpper_bpart g).2 i).1.le, ((positiveUpper_bpart g).2 i).2⟩⟩
    · rintro ⟨htri, hd⟩
      apply kpart_eq
      refine ⟨htri, fun i => ⟨?_, (hd i).2⟩⟩
      apply lt_of_le_of_ne (hd i).1
      intro he
      have hz : b (g, k) i i = 0 := Complex.ext (by simpa using he.symm)
        (by simpa using (hd i).2)
      have hdet : (b (g, k)).det ≠ 0 :=
        ((Matrix.isUnit_iff_isUnit_det _).mp (g * (k : G)⁻¹).isUnit).ne_zero
      rw [Matrix.det_of_isUpperTriangular htri] at hdet
      exact hdet (Finset.prod_eq_zero (Finset.mem_univ i) hz)
  apply continuous_of_isClosed_graph
  rw [hEq]
  exact IsClosed.inter (isClosed_setOfPred_blockTriangular.preimage hb)
    (isClosed_iInter fun i => (isClosed_le continuous_const (Complex.continuous_re.comp (hc i))).inter
      (isClosed_eq (Complex.continuous_im.comp (hc i)) continuous_const))

/-! ### Logarithmic and unipotent coordinates -/

/-- The upper triangular factor with positive diagonal. -/
def bpart (g : G) : G :=
  g * (kpart g : G)⁻¹

theorem bpart_mul_kpart (g : G) : bpart g * (kpart g : G) = g := by
  rw [bpart, inv_mul_cancel_right]

/-- Logarithms of the positive diagonal entries of the triangular factor. -/
def alpha (g : G) : Fin n → ℝ :=
  fun i => Real.log ((bpart g).val i i).re

theorem exp_alpha (g : G) (i : Fin n) : (Real.exp (alpha g i) : ℂ) = (bpart g).val i i := by
  have hp : 0 < ((bpart g).val i i).re := ((positiveUpper_bpart g).2 i).1
  exact (congrArg Complex.ofReal (Real.exp_log hp)).trans
    (diag_eq_real (positiveUpper_bpart g) i).symm

private theorem npart_mem (g : G) : bpart g * (logTorus (alpha g))⁻¹ ∈ N := by
  refine ⟨?_, fun i => ?_⟩
  · rw [Units.val_mul, logTorus_inv_val]
    exact LinearAlgebra.TriangularUnitary.isUpperTriangular_mul_diagonal
      (positiveUpper_bpart g).1 _
  · change ((bpart g).val * (logTorus (alpha g))⁻¹.val) i i = 1
    rw [logTorus_inv_val, Matrix.mul_diagonal, Real.exp_neg, Complex.ofReal_inv, exp_alpha]
    exact mul_inv_cancel₀ (by
      intro h
      have := congrArg Complex.re h
      exact ((positiveUpper_bpart g).2 i).1.ne' this)

/-- The upper unipotent factor of the positive-diagonal Iwasawa decomposition. -/
def npart (g : G) : N :=
  ⟨bpart g * (logTorus (alpha g))⁻¹, npart_mem g⟩

theorem npart_mul_logTorus_mul_kpart (g : G) :
    (npart g : G) * logTorus (alpha g) * (kpart g : G) = g := by
  change bpart g * (logTorus (alpha g))⁻¹ * logTorus (alpha g) * (kpart g : G) = g
  rw [inv_mul_cancel_right, bpart_mul_kpart]

theorem kpart_iwasawa (u : N) (y : Fin n → ℝ) (k : K) :
    kpart ((u : G) * logTorus y * (k : G)) = k := by
  apply kpart_eq
  rw [mul_inv_cancel_right, Units.val_mul]
  exact (unipotent_positiveUpper u).mul (logTorus_positiveUpper y)

theorem bpart_iwasawa (u : N) (y : Fin n → ℝ) (k : K) :
    bpart ((u : G) * logTorus y * (k : G)) = (u : G) * logTorus y := by
  rw [bpart, kpart_iwasawa, mul_inv_cancel_right]

theorem alpha_iwasawa (u : N) (y : Fin n → ℝ) (k : K) :
    alpha ((u : G) * logTorus y * (k : G)) = y := by
  funext i
  change Real.log ((bpart ((u : G) * logTorus y * (k : G))).val i i).re = y i
  rw [bpart_iwasawa, Units.val_mul, logTorus_val, Matrix.mul_diagonal,
    GeneralLinear.UpperUnipotent.entry_diag u i, one_mul, Complex.ofReal_re, Real.log_exp]

theorem npart_iwasawa (u : N) (y : Fin n → ℝ) (k : K) :
    npart ((u : G) * logTorus y * (k : G)) = u := by
  apply Subtype.ext
  change bpart ((u : G) * logTorus y * (k : G)) *
    (logTorus (alpha ((u : G) * logTorus y * (k : G))))⁻¹ = (u : G)
  rw [bpart_iwasawa, alpha_iwasawa, mul_inv_cancel_right]

theorem continuous_bpart : Continuous (bpart (n := n)) :=
  continuous_id.mul (continuous_subtype_val.comp continuous_kpart).inv

theorem continuous_alpha : Continuous (alpha (n := n)) := by
  have hb : Continuous (fun g : G => (bpart g).val) :=
    (show Continuous (Units.val : G → Mat) from Units.continuous_val).comp continuous_bpart
  refine continuous_pi fun i => ?_
  exact (Complex.continuous_re.comp ((continuous_apply_apply i i).comp
    hb)).log fun g => ((positiveUpper_bpart g).2 i).1.ne'

theorem continuous_npart : Continuous (npart (n := n)) :=
  Continuous.subtype_mk (continuous_bpart.mul (continuous_logTorus.comp continuous_alpha).inv) _

/-- Ordered Iwasawa factorization of the complex matrix group as a homeomorphism. -/
def iwasawaHomeomorph (n : ℕ) :
    (Langlands.GeneralLinear.upperUnipotent n ℂ × ((Fin n → ℝ) × unitaryCompact ℂ n)) ≃ₜ
      Langlands.GeneralLinear n ℂ where
  toFun p := p.1.val * logTorus p.2.1 * p.2.2.val
  invFun g := (npart g, alpha g, kpart g)
  left_inv p := by
    rcases p with ⟨u, y, k⟩
    change (npart _, alpha _, kpart _) = (u, y, k)
    rw [npart_iwasawa, alpha_iwasawa, kpart_iwasawa]
  right_inv := npart_mul_logTorus_mul_kpart
  continuous_toFun :=
    ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_logTorus.comp (continuous_fst.comp continuous_snd))).mul
      (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
  continuous_invFun := continuous_npart.prodMk (continuous_alpha.prodMk continuous_kpart)

/-! ### Left multiplication and descent to the quotient -/

theorem alpha_unipotent_mul (u : N) (g : G) : alpha ((u : G) * g) = alpha g := by
  conv_lhs => rw [← npart_mul_logTorus_mul_kpart g]
  rw [← mul_assoc, ← mul_assoc]
  exact alpha_iwasawa (u * npart g) _ _

theorem kpart_unipotent_mul (u : N) (g : G) : kpart ((u : G) * g) = kpart g := by
  conv_lhs => rw [← npart_mul_logTorus_mul_kpart g]
  rw [← mul_assoc, ← mul_assoc]
  exact kpart_iwasawa (u * npart g) _ _

theorem npart_unipotent_mul (u : N) (g : G) : npart ((u : G) * g) = u * npart g := by
  conv_lhs => rw [← npart_mul_logTorus_mul_kpart g]
  rw [← mul_assoc, ← mul_assoc]
  exact npart_iwasawa (u * npart g) _ _

private def torusUnits (y : Fin n → ℝ) : Fin n → ℂˣ :=
  fun i => Units.mk0 (Real.exp (y i) : ℂ) (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))

/-- Conjugation of the unipotent group by a positive diagonal. -/
def conjTorus (z : Fin n → ℝ) : N ≃* N :=
  Langlands.RankinSelberg.diagonalConj (torusUnits z)

theorem conjTorus_val (z : Fin n → ℝ) (u : N) :
    (conjTorus z u : G) = logTorus z * (u : G) * (logTorus z)⁻¹ :=
  Langlands.RankinSelberg.diagonalConj_val (torusUnits z) u

theorem continuous_conjTorus (z : Fin n → ℝ) : Continuous (conjTorus z) :=
  Langlands.RankinSelberg.continuous_diagonalConj (torusUnits z)

theorem conjTorus_neg (z : Fin n → ℝ) (u : N) : conjTorus (-z) (conjTorus z u) = u := by
  apply Subtype.ext
  rw [conjTorus_val, conjTorus_val, logTorus_neg]
  group

theorem torus_mul_eq (z : Fin n → ℝ) (g : G) :
    logTorus z * g =
      (conjTorus z (npart g) : G) * logTorus (z + alpha g) * (kpart g : G) := by
  conv_lhs => rw [← npart_mul_logTorus_mul_kpart g]
  rw [conjTorus_val, logTorus_add]
  group

theorem alpha_torus_mul (z : Fin n → ℝ) (g : G) : alpha (logTorus z * g) = z + alpha g := by
  rw [torus_mul_eq, alpha_iwasawa]

theorem npart_torus_mul (z : Fin n → ℝ) (g : G) :
    npart (logTorus z * g) = conjTorus z (npart g) := by
  rw [torus_mul_eq, npart_iwasawa]

theorem mk_eq_mk_logTorus_mul_kpart (g : G) :
    Quotient.mk (QuotientGroup.rightRel N) g =
      Quotient.mk _ (logTorus (alpha g) * (kpart g : G)) := by
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  have h : logTorus (alpha g) * (kpart g : G) = (npart g : G)⁻¹ * g := by
    rw [eq_inv_mul_iff_mul_eq, ← mul_assoc]
    exact npart_mul_logTorus_mul_kpart g
  rw [h, mul_inv_cancel_right]
  exact inv_mem (npart g).2

/-- Continuous logarithmic toral and unitary coordinates on the left unipotent quotient. -/
def quotientHomeomorph (n : ℕ) :
    LeftQuotient (Langlands.GeneralLinear.upperUnipotent n ℂ) ≃ₜ
      ((Fin n → ℝ) × unitaryCompact ℂ n) where
  toFun := descend _ (fun g => (alpha g, kpart g))
    (fun u g => Prod.ext (alpha_unipotent_mul u g) (kpart_unipotent_mul u g))
  invFun p := Quotient.mk _ (logTorus p.1 * p.2.val)
  left_inv := Quotient.ind (fun g => (mk_eq_mk_logTorus_mul_kpart g).symm)
  right_inv p := by
    change (alpha (logTorus p.1 * p.2.val), kpart (logTorus p.1 * p.2.val)) = p
    exact Prod.ext
      (by simpa only [OneMemClass.coe_one, one_mul] using alpha_iwasawa 1 p.1 p.2)
      (by simpa only [OneMemClass.coe_one, one_mul] using kpart_iwasawa 1 p.1 p.2)
  continuous_toFun := (continuous_alpha.prodMk continuous_kpart).quotient_lift _
  continuous_invFun := continuous_quotient_mk'.comp
    ((continuous_logTorus.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd))

/-- The logarithmic toral coordinate on the left unipotent quotient. -/
def alphaQ : LeftQuotient N → (Fin n → ℝ) :=
  fun q => (quotientHomeomorph n q).1

@[simp] theorem alphaQ_mk (g : G) :
    alphaQ (Quotient.mk (QuotientGroup.rightRel N) g) = alpha g := rfl

theorem continuous_alphaQ : Continuous (alphaQ (n := n)) :=
  continuous_fst.comp (quotientHomeomorph n).continuous

theorem isCompact_alphaQ_preimage {C : Set (Fin n → ℝ)} (hC : IsCompact C) :
    IsCompact ((alphaQ (n := n)) ⁻¹' C) := by
  have hset : (alphaQ (n := n)) ⁻¹' C = (quotientHomeomorph n) ⁻¹' (C ×ˢ Set.univ) := by
    ext q
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
    rfl
  rw [hset]
  exact (quotientHomeomorph n).isCompact_preimage.mpr (hC.prod isCompact_univ)

end Langlands.Global.RankinSelbergGlobal.ComplexLocalIwasawa
