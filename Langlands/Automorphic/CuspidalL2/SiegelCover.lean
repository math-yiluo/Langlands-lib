import Langlands.Automorphic.CuspidalL2.Representation
import Langlands.Global.AdelicGLSiegelShape
import Langlands.Global.AdelicRepresentationHeightPropernessProof
import Langlands.Global.AdeleQuotientCompactProof
import Langlands.Automorphic.CuspidalL2.CompactCover
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! # Square integrability of cusp forms on determinant bands via Siegel sets -/

noncomputable section
universe u
set_option autoImplicit false

open scoped Classical NNReal Pointwise RestrictedProduct
open NumberField

namespace Langlands.Automorphic.CuspidalL2

/-! ### Elementary estimates on real vectors -/

/-- Telescoping: if every step `x i - x (i+1)` is at most `B ≥ 0`, then `x i - x j ≤ n B`
for all `i ≤ j`. -/
theorem sub_le_of_adjacent {n : ℕ} (x : Fin n → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ i j : Fin n, i.val + 1 = j.val → x i - x j ≤ B) :
    ∀ i j : Fin n, i ≤ j → x i - x j ≤ n * B := by
  have key : ∀ k : ℕ, ∀ i j : Fin n, j.val = i.val + k → x i - x j ≤ k * B := by
    intro k
    induction k with
    | zero =>
      intro i j hij
      have : i = j := Fin.ext (by omega)
      subst this
      simp
    | succ k ih =>
      intro i j hij
      have h1 := ih i ⟨i.val + k, by omega⟩ rfl
      have h2 := h ⟨i.val + k, by omega⟩ j (by simp only; omega)
      push_cast
      linarith
  intro i j hij
  have hle : i.val ≤ j.val := hij
  have hk := key (j.val - i.val) i j (by omega)
  have hkn : ((j.val - i.val : ℕ) : ℝ) ≤ n := by
    have := j.isLt
    exact_mod_cast (by omega : j.val - i.val ≤ n)
  exact hk.trans (mul_le_mul_of_nonneg_right hkn hB)

/-- The archimedean chamber condition: consecutive increases `x (i+1) - x i` are at most `K`. -/
def Chamber {n : ℕ} (K : ℝ) (x : Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, i.val + 1 = j.val → x j - x i ≤ K

/-- In the chamber, bounded consecutive drops bound all differences. -/
theorem sub_le_of_chamber {n : ℕ} {K D : ℝ} (hK : 0 ≤ K) (hD : 0 ≤ D) (x : Fin n → ℝ)
    (hx : Chamber K x) (hdrop : ∀ i j : Fin n, i.val + 1 = j.val → x i - x j ≤ D) :
    ∀ i j : Fin n, x i - x j ≤ n * (K + D) := by
  intro i j
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rcases le_total i j with hij | hji
  · have := sub_le_of_adjacent x hD hdrop i j hij
    nlinarith
  · have := sub_le_of_adjacent (fun k => -x k) hK
      (fun a b hab => by have := hx a b hab; show -x a - -x b ≤ K; linarith) j i hji
    have h' : x i - x j ≤ n * K := by linarith
    nlinarith

/-- Bounded differences and a bounded sum bound every coordinate. -/
theorem abs_le_of_sub_le {n : ℕ} (x : Fin n → ℝ) {T R : ℝ}
    (hT : ∀ i j, x i - x j ≤ T) (hR : |∑ i, x i| ≤ R) (i : Fin n) :
    |x i| ≤ R + n * T := by
  have h1 : (n : ℝ) * x i - ∑ j, x j ≤ n * T := by
    have : (n : ℝ) * x i - ∑ j, x j = ∑ j, (x i - x j) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    rw [this]
    calc ∑ j, (x i - x j) ≤ ∑ _j : Fin n, T := Finset.sum_le_sum fun j _ => hT i j
      _ = n * T := by simp
  have h2 : ∑ j, x j - (n : ℝ) * x i ≤ n * T := by
    have : ∑ j, x j - (n : ℝ) * x i = ∑ j, (x j - x i) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    rw [this]
    calc ∑ j, (x j - x i) ≤ ∑ _j : Fin n, T := Finset.sum_le_sum fun j _ => hT j i
      _ = n * T := by simp
  have hn : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr (Fin.pos i)
  have habs := abs_le.mp hR
  have hx : |x i| ≤ |(n : ℝ) * x i| := by
    rw [abs_mul, Nat.abs_cast]
    exact le_mul_of_one_le_left (abs_nonneg _) hn
  have : |(n : ℝ) * x i| ≤ R + n * T := abs_le.mpr ⟨by linarith, by linarith⟩
  linarith

end Langlands.Automorphic.CuspidalL2

namespace Langlands.Global

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

/-! ### Heights and determinants of the archimedean torus -/

omit [NumberField F] in
theorem torInf_nsmul (y : Fin n → ℝ) (k : ℕ) : torInf F n ((k : ℝ) • y) = torInf F n y ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have : ((k + 1 : ℕ) : ℝ) • y = (k : ℝ) • y + y := by push_cast; rw [add_smul, one_smul]
    rw [this, torInf_add, ih, pow_succ]

theorem matrixHeight_pow_succ_le (g : InfiniteAdelicGL F n) (k : ℕ) :
    ArchimedeanGL.matrixHeight F n (g ^ (k + 1)) ≤ ArchimedeanGL.matrixHeight F n g ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ g (k + 1), pow_succ _ (k + 1)]
    exact (ArchimedeanGL.matrixHeight_mul_le F n _ _).trans
      (mul_le_mul_of_nonneg_right ih (ArchimedeanGL.matrixHeight_nonneg F n g))

/-- The height of the archimedean torus grows at most exponentially in `∑ |x i|`. -/
theorem exists_matrixHeight_torInf_le :
    ∃ C₀ c₀ : ℝ, 0 ≤ C₀ ∧ 0 ≤ c₀ ∧ ∀ x : Fin n → ℝ,
      ArchimedeanGL.matrixHeight F n (torInf F n x) ≤ C₀ * Real.exp (c₀ * ∑ i, |x i|) := by
  have hbox : IsCompact (Set.univ.pi fun _ : Fin n => Set.Icc (-1 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hcont : Continuous fun y : Fin n → ℝ => ArchimedeanGL.matrixHeight F n (torInf F n y) :=
    (ArchimedeanGL.continuous_matrixHeight F n).comp (continuous_torInf F n)
  obtain ⟨M, hM⟩ := (hbox.image hcont).bddAbove
  set M₀ := max 1 M with hM₀
  have hM₀1 : 1 ≤ M₀ := le_max_left _ _
  have hM₀pos : 0 < M₀ := zero_lt_one.trans_le hM₀1
  refine ⟨M₀ ^ 2, Real.log M₀, by positivity, Real.log_nonneg hM₀1, fun x => ?_⟩
  set s := ∑ i, |x i| with hs
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun i _ => abs_nonneg _
  set k := ⌈s⌉₊ + 1 with hk
  have hkpos : (0 : ℝ) < k := by positivity
  have hks : s ≤ k := by
    rw [hk]; push_cast; linarith [Nat.le_ceil s]
  have hk2 : (k : ℝ) ≤ s + 2 := by
    rw [hk]; push_cast; linarith [Nat.ceil_lt_add_one hs0]
  set y : Fin n → ℝ := (k : ℝ)⁻¹ • x with hy
  have hxy : x = (k : ℝ) • y := by
    rw [hy, smul_smul, mul_inv_cancel₀ hkpos.ne', one_smul]
  have hybox : y ∈ Set.univ.pi fun _ : Fin n => Set.Icc (-1 : ℝ) 1 := by
    intro i _
    have hxi : |x i| ≤ s := Finset.single_le_sum (f := fun i => |x i|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    have : |y i| ≤ 1 := by
      rw [hy, Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, Nat.abs_cast,
        inv_mul_le_iff₀ hkpos, mul_one]
      exact hxi.trans hks
    exact abs_le.mp this
  have hHy : ArchimedeanGL.matrixHeight F n (torInf F n y) ≤ M₀ :=
    (hM ⟨y, hybox, rfl⟩).trans (le_max_right _ _)
  obtain ⟨k', hk'⟩ : ∃ k' : ℕ, k = k' + 1 := ⟨⌈s⌉₊, rfl⟩
  have hpow : ArchimedeanGL.matrixHeight F n (torInf F n x) ≤ M₀ ^ k := by
    rw [hxy, torInf_nsmul, hk']
    exact (matrixHeight_pow_succ_le F n _ k').trans
      (pow_le_pow_left₀ (ArchimedeanGL.matrixHeight_nonneg F n _) hHy _)
  refine hpow.trans ?_
  have hlog : 0 ≤ Real.log M₀ := Real.log_nonneg hM₀1
  calc M₀ ^ k = Real.exp (k * Real.log M₀) := by
        rw [Real.exp_nat_mul, Real.exp_log hM₀pos]
    _ ≤ Real.exp ((s + 2) * Real.log M₀) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hk2 hlog)
    _ = M₀ ^ 2 * Real.exp (Real.log M₀ * s) := by
        have h2 : Real.exp (2 * Real.log M₀) = M₀ ^ 2 := by
          rw [show (2 : ℝ) * Real.log M₀ = ((2 : ℕ) : ℝ) * Real.log M₀ by norm_num,
            Real.exp_nat_mul, Real.exp_log hM₀pos]
        rw [add_mul, Real.exp_add, h2, mul_comm s]
        exact mul_comm _ _

/-- The idelic absolute value of the determinant. -/
def absDet (g : AdelicGL F n) : ℝ :=
  ((IdeleAbsoluteValue.full F (AdelicGL.determinant F n g) : ℝ≥0) : ℝ)

theorem absDet_mul (g h : AdelicGL F n) : absDet F n (g * h) = absDet F n g * absDet F n h := by
  simp only [absDet, map_mul, Units.val_mul, NNReal.coe_mul]

theorem absDet_pos (g : AdelicGL F n) : 0 < absDet F n g :=
  IdeleAbsoluteValue.full_pos F _

theorem continuous_absDet : Continuous (absDet F n) :=
  NNReal.continuous_coe.comp (Units.continuous_val.comp
    ((IdeleAbsoluteValue.full F).continuous.comp (AdelicGL.determinant F n).continuous))

theorem determinant_rational (γ : RationalGL F n) :
    AdelicGL.determinant F n (AdelicGL.rational F n γ) =
      diagonalUnits F (Matrix.GeneralLinearGroup.det γ) := by
  apply Units.ext
  exact (RingHom.map_det (algebraMap F (Adeles F)) γ.val).symm

theorem absDet_rational_mul (γ : RationalGL F n) (g : AdelicGL F n) :
    absDet F n (AdelicGL.rational F n γ * g) = absDet F n g := by
  rw [absDet_mul]
  have : absDet F n (AdelicGL.rational F n γ) = 1 := by
    rw [absDet, determinant_rational, IdeleAbsoluteValue.full_diagonalUnits]
    rfl
  rw [this, one_mul]

theorem determinant_ofInfinite_torInf (x : Fin n → ℝ) :
    AdelicGL.determinant F n (AdelicGL.ofInfinite F n (torInf F n x)) =
      PositiveRealIdeles.full F (expUnit (∑ i, x i)) := by
  apply Units.ext
  apply Prod.ext
  · have h1 : ((AdelicGL.determinant F n (AdelicGL.ofInfinite F n (torInf F n x)) :
          Adeles F)).1 =
        Matrix.det ((AdelicGL.infinite F n (AdelicGL.ofInfinite F n (torInf F n x)) :
          Matrix (Fin n) (Fin n) (InfiniteAdeles F))) :=
      RingHom.map_det (RingHom.fst (InfiniteAdeleRing F) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) _
    rw [h1, AdelicGL.infinite_ofInfinite, torInf_val, Matrix.det_diagonal, ← map_prod,
      ← Real.exp_sum]
    rfl
  · have h2 : ((AdelicGL.determinant F n (AdelicGL.ofInfinite F n (torInf F n x)) :
          Adeles F)).2 =
        Matrix.det ((AdelicGL.finite F n (AdelicGL.ofInfinite F n (torInf F n x)) :
          Matrix (Fin n) (Fin n) (FiniteAdeles F))) :=
      RingHom.map_det (RingHom.snd (InfiniteAdeleRing F) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) _
    rw [h2, AdelicGL.finite_ofInfinite, Units.val_one, Matrix.det_one]
    rfl

theorem absDet_ofInfinite_torInf (x : Fin n → ℝ) :
    absDet F n (AdelicGL.ofInfinite F n (torInf F n x)) =
      Real.exp (∑ i, x i) ^ Module.finrank ℚ F := by
  rw [absDet, determinant_ofInfinite_torInf, PositiveRealIdeles.absoluteValue_full,
    Units.val_pow_eq_pow_val, NNReal.coe_pow, coe_expUnit]

/-! ### The Siegel decomposition in torus coordinates -/

/-- A real scalar inserted at every infinite place, with finite part `1`. -/
def realScale (s : ℝ) : Adeles F :=
  ((PositiveRealIdeles.infiniteRealEmbedding F s, 1) :
    InfiniteAdeleRing F × IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)

theorem realScale_mul (s t : ℝ) : realScale F (s * t) = realScale F s * realScale F t :=
  Prod.ext (map_mul _ _ _) (mul_one 1).symm

theorem realScale_zero_mul (s : ℝ) (a : Adeles F) (ha : a = 0) :
    realScale F s * a = realScale F 0 * a := by
  rw [ha, mul_zero, mul_zero]

theorem continuous_realScale : Continuous (realScale F) :=
  (PositiveRealIdeles.continuous_infiniteRealEmbedding F).prodMk continuous_const

omit [NumberField F] in
theorem torInf_neg (x : Fin n → ℝ) : torInf F n (-x) = (torInf F n x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← torInf_add, neg_add_cancel, torInf_zero])

theorem ofInfinite_torInf_val (x : Fin n → ℝ) :
    ((AdelicGL.ofInfinite F n (torInf F n x) : AdelicGL F n) :
        Matrix (Fin n) (Fin n) (Adeles F)) =
      Matrix.diagonal fun i => realScale F (Real.exp (x i)) := by
  ext i j
  apply Prod.ext
  · change AdelicGL.infinite F n (AdelicGL.ofInfinite F n (torInf F n x)) i j = _
    rw [AdelicGL.infinite_ofInfinite, torInf_val]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq]
      rfl
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij]
      rfl
  · change AdelicGL.finite F n (AdelicGL.ofInfinite F n (torInf F n x)) i j = _
    rw [AdelicGL.finite_ofInfinite]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
      exact Matrix.one_apply_eq i
    · rw [Matrix.diagonal_apply_ne _ hij]
      exact Matrix.one_apply_ne hij

/-- Conjugation by the torus rescales the `(i, j)` entry by `e^{x_j - x_i}`. -/
theorem ofInfinite_torInf_conj_apply (x : Fin n → ℝ) (M : Matrix (Fin n) (Fin n) (Adeles F))
    (i j : Fin n) :
    ((((AdelicGL.ofInfinite F n (torInf F n x))⁻¹ : AdelicGL F n) :
        Matrix (Fin n) (Fin n) (Adeles F)) * M *
      ((AdelicGL.ofInfinite F n (torInf F n x) : AdelicGL F n) :
        Matrix (Fin n) (Fin n) (Adeles F))) i j =
      realScale F (Real.exp (x j - x i)) * M i j := by
  rw [← map_inv, ← torInf_neg, ofInfinite_torInf_val, ofInfinite_torInf_val, Matrix.mul_diagonal,
    Matrix.diagonal_mul, mul_right_comm, ← realScale_mul, ← Real.exp_add, Pi.neg_apply,
    neg_add_eq_sub]

theorem continuous_diagonalGL :
    Continuous fun ω : Fin n → Ideles F =>
      (PrimitiveAdelicHeight.diagonalGL ω : AdelicGL F n) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun ω : Fin n → Ideles F =>
      Matrix.diagonal fun i => ((ω i : Ideles F) : Adeles F)
    exact Continuous.matrix_diagonal
      (continuous_pi fun i => Units.continuous_val.comp (continuous_apply i))
  · change Continuous fun ω : Fin n → Ideles F =>
      Matrix.diagonal fun i => (((ω i)⁻¹ : Ideles F) : Adeles F)
    exact Continuous.matrix_diagonal
      (continuous_pi fun i => Units.continuous_coe_inv.comp (continuous_apply i))

/-- Entries of a torus conjugate of an upper triangular matrix in the chamber. -/
theorem conj_apply_mem {K : ℝ} (hK : 0 ≤ K) {x : Fin n → ℝ} (hx : Automorphic.CuspidalL2.Chamber K x)
    (E₀ : Set (Adeles F)) (M : Matrix (Fin n) (Fin n) (Adeles F)) (hM : M.IsUpperTriangular)
    (hME : ∀ i j, M i j ∈ E₀) (i j : Fin n) :
    ((((AdelicGL.ofInfinite F n (torInf F n x))⁻¹ : AdelicGL F n) :
        Matrix (Fin n) (Fin n) (Adeles F)) * M *
      ((AdelicGL.ofInfinite F n (torInf F n x) : AdelicGL F n) :
        Matrix (Fin n) (Fin n) (Adeles F))) i j ∈
      (fun p : ℝ × Adeles F => realScale F p.1 * p.2) ''
        (Set.Icc 0 (Real.exp (n * K)) ×ˢ E₀) := by
  rw [ofInfinite_torInf_conj_apply]
  rcases le_or_gt i j with hij | hji
  · have hb : -x i - -x j ≤ n * K := Automorphic.CuspidalL2.sub_le_of_adjacent (fun k => -x k) hK
      (fun a b hab => by have := hx a b hab; show -x a - -x b ≤ K; linarith) i j hij
    refine ⟨(Real.exp (x j - x i), M i j), ⟨⟨(Real.exp_pos _).le, ?_⟩, hME i j⟩, rfl⟩
    exact Real.exp_le_exp.mpr (by linarith)
  · refine ⟨(0, M i j), ⟨⟨le_rfl, (Real.exp_pos _).le⟩, hME i j⟩, ?_⟩
    exact (realScale_zero_mul F _ _ (hM hji)).symm

/-- **Siegel decomposition in torus coordinates.** Every adelic matrix is, after a rational
left translation, an archimedean torus element `torInf x` in a chamber times an element of a
fixed compact set. -/
theorem exists_siegelDecomposition :
    ∃ (Q₁ : Set (AdelicGL F n)) (K : ℝ), IsCompact Q₁ ∧ 0 ≤ K ∧
      ∀ g : AdelicGL F n, ∃ (γ : RationalGL F n) (x : Fin n → ℝ) (q : AdelicGL F n),
        q ∈ Q₁ ∧ AdelicGL.rational F n γ * g = AdelicGL.ofInfinite F n (torInf F n x) * q ∧
          Automorphic.CuspidalL2.Chamber K x := by
  obtain ⟨ΩN, C, c, hΩ, hΩN, hC, -, hc, hsiegel⟩ :=
    PrimitiveAdelicHeight.exists_rational_mul_mem_siegelSetGL F n
  have hd : 0 < Module.finrank ℚ F := Module.finrank_pos
  set K : ℝ := max 0 (Real.log c / Module.finrank ℚ F) with hKdef
  have hK : 0 ≤ K := le_max_left _ _
  set E₀ : Set (Adeles F) := ⋃ i : Fin n, ⋃ j : Fin n,
    ((fun N : Matrix (Fin n) (Fin n) (Adeles F) => N i j) '' ΩN ∪
      (fun N : Matrix (Fin n) (Fin n) (Adeles F) => N.adjugate i j) '' ΩN) with hE₀def
  have hE₀ : IsCompact E₀ := isCompact_iUnion fun i => isCompact_iUnion fun j =>
    (hΩ.image (continuous_id.matrix_elem i j)).union
      (hΩ.image (continuous_id.matrix_adjugate.matrix_elem i j))
  set E : Set (Adeles F) := (fun p : ℝ × Adeles F => realScale F p.1 * p.2) ''
    (Set.Icc 0 (Real.exp (n * K)) ×ˢ E₀) with hEdef
  have hE : IsCompact E := (isCompact_Icc.prod hE₀).image
    (((continuous_realScale F).comp continuous_fst).mul continuous_snd)
  set W₁ : Set (AdelicGL F n) :=
    (fun ω : Fin n → Ideles F => (PrimitiveAdelicHeight.diagonalGL ω : AdelicGL F n)) ''
      Set.univ.pi fun _ => C with hW₁def
  have hW₁ : IsCompact W₁ := (isCompact_univ_pi fun _ => hC).image (continuous_diagonalGL F n)
  refine ⟨AdelicMatrixHeight.entryBox F n E * W₁ * (PrimitiveAdelicHeight.standardCompact F n : Set (AdelicGL F n)),
    K, ((AdelicMatrixHeight.isCompact_entryBox F n hE).mul hW₁).mul
      (PrimitiveAdelicHeight.isCompact_standardCompact F n), hK, fun g => ?_⟩
  obtain ⟨γ, hγ⟩ := hsiegel g
  obtain ⟨N, ω, r, κ, hh, hN, hω, hκ, hr⟩ := hγ
  obtain ⟨x, hx⟩ : ∃ x : Fin n → ℝ, ∀ i, r i = expUnit (x i) :=
    ⟨fun i => Real.log ((r i : ℝ≥0) : ℝ), fun i => by
      apply Units.ext
      apply NNReal.eq
      rw [coe_expUnit, Real.exp_log (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (r i).ne_zero))]⟩
  have hrx : r = fun i => expUnit (x i) := funext hx
  subst hrx
  -- the chamber condition
  have hch : Automorphic.CuspidalL2.Chamber K x := by
    intro i j hij
    have h1 := hr i j hij
    rw [PositiveRealIdeles.absoluteValue_full, PositiveRealIdeles.absoluteValue_full,
      Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, NNReal.coe_pow, NNReal.coe_pow,
      coe_expUnit, coe_expUnit, ← Real.exp_nat_mul, ← Real.exp_nat_mul] at h1
    have h2 : (Module.finrank ℚ F : ℝ) * x j ≤ Real.log c + Module.finrank ℚ F * x i := by
      have := Real.log_le_log (Real.exp_pos _) h1
      rwa [Real.log_exp, Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp] at this
    have hdpos : (0 : ℝ) < Module.finrank ℚ F := Nat.cast_pos.mpr hd
    have : x j - x i ≤ Real.log c / Module.finrank ℚ F := by
      rw [le_div_iff₀ hdpos]; linarith
    exact this.trans (le_max_right _ _)
  set h := AdelicGL.rational F n γ * g with hhdef
  set A := AdelicGL.ofInfinite F n (torInf F n x) with hAdef
  set W : AdelicGL F n := PrimitiveAdelicHeight.diagonalGL ω with hWdef
  have hAval : (A : Matrix (Fin n) (Fin n) (Adeles F)) =
      Matrix.diagonal fun i => ((PositiveRealIdeles.full F (expUnit (x i)) : Ideles F) :
        Adeles F) :=
    ofInfinite_torInf_val F n x
  have hWA : W * A = A * W := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hAval]
    change Matrix.diagonal (fun i => ((ω i : Ideles F) : Adeles F)) * _ =
      _ * Matrix.diagonal (fun i => ((ω i : Ideles F) : Adeles F))
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  set Ngl := h * κ⁻¹ * (W * A)⁻¹ with hNgldef
  have hNgl : (Ngl : Matrix (Fin n) (Fin n) (Adeles F)) = N := by
    have e1 : (Ngl : Matrix (Fin n) (Fin n) (Adeles F)) =
        (h : Matrix (Fin n) (Fin n) (Adeles F)) *
          ((κ⁻¹ : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F)) *
          (((W * A)⁻¹ : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F)) := by
      rw [hNgldef, Units.val_mul, Units.val_mul]
    have e2 : (h : Matrix (Fin n) (Fin n) (Adeles F)) =
        N * ((W * A : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F)) *
          (κ : Matrix (Fin n) (Fin n) (Adeles F)) := by
      rw [hh, Units.val_mul, hAval, ← Matrix.mul_assoc]
      rfl
    rw [e1, e2, Units.mul_inv_cancel_right, Units.mul_inv_cancel_right]
  have hdet : N.det = 1 := PrimitiveAdelicHeight.IsUnitriangular.det_eq_one (hΩN N hN)
  have hNtri : N.IsUpperTriangular := (hΩN N hN).1
  have hNinv : ((Ngl⁻¹ : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F)) = N.adjugate := by
    rw [Matrix.coe_units_inv, hNgl, Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
  have hadjtri : N.adjugate.IsUpperTriangular := by
    have : Invertible (Ngl : Matrix (Fin n) (Fin n) (Adeles F)) := Units.invertible Ngl
    have h1 := Matrix.blockTriangular_inv_of_blockTriangular
      (M := (Ngl : Matrix (Fin n) (Fin n) (Adeles F))) (hNgl ▸ hNtri)
    rwa [← Matrix.coe_units_inv, hNinv] at h1
  refine ⟨γ, x, (A⁻¹ * Ngl * A) * W * κ, ?_, ?_, hch⟩
  · refine Set.mul_mem_mul (Set.mul_mem_mul ⟨fun i j => ?_, fun i j => ?_⟩
      ⟨ω, fun i _ => hω i, rfl⟩) hκ
    · rw [Units.val_mul, Units.val_mul, hNgl]
      exact conj_apply_mem F n hK hch E₀ N hNtri
        (fun i j => Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, Or.inl ⟨N, hN, rfl⟩⟩⟩) i j
    · have : (A⁻¹ * Ngl * A)⁻¹ = A⁻¹ * Ngl⁻¹ * A := by group
      rw [this, Units.val_mul, Units.val_mul, hNinv]
      exact conj_apply_mem F n hK hch E₀ N.adjugate hadjtri
        (fun i j => Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, Or.inr ⟨N, hN, rfl⟩⟩⟩) i j
  · show h = A * ((A⁻¹ * Ngl * A) * W * κ)
    rw [hNgldef, hWA]
    group

end Langlands.Global

namespace Langlands.Automorphic.CuspidalL2

/-! ### Drops and the two regimes of the chamber -/

/-- The drop `x (a - 1) - x a` at a positive index `a` (and `0` at the index `0`). -/
def chamberDrop {n : ℕ} (x : Fin n → ℝ) (a : Fin n) : ℝ :=
  if h : 0 < a.val then x ⟨a.val - 1, by omega⟩ - x a else 0

theorem chamberDrop_of_succ {n : ℕ} (x : Fin n → ℝ) (i j : Fin n) (hij : i.val + 1 = j.val) :
    chamberDrop x j = x i - x j := by
  have hj : 0 < j.val := by omega
  have hi : (⟨j.val - 1, by omega⟩ : Fin n) = i := Fin.ext (by simp only; omega)
  simp only [chamberDrop, hj, ↓reduceDIte, hi]

/-- Across a drop at `a`, every gap `x j - x i` with `i < a ≤ j` is at most `2 n K` minus the
drop. -/
theorem gap_le_of_chamber {n : ℕ} {K : ℝ} (hK : 0 ≤ K) (x : Fin n → ℝ) (hx : Chamber K x)
    (a : Fin n) (ha : 0 < a.val) (i j : Fin n) (hi : i.val < a.val) (hj : a.val ≤ j.val) :
    x j - x i ≤ 2 * n * K - chamberDrop x a := by
  have hneg : ∀ i j : Fin n, i ≤ j → x j - x i ≤ n * K := fun i j hij => by
    have := sub_le_of_adjacent (fun k => -x k) hK
      (fun a b hab => by have := hx a b hab; show -x a - -x b ≤ K; linarith) i j hij
    linarith
  have h1 := hneg a j hj
  have h2 := hneg i ⟨a.val - 1, by omega⟩ (show i.val ≤ a.val - 1 by omega)
  have h3 : chamberDrop x a = x ⟨a.val - 1, by omega⟩ - x a := by
    simp only [chamberDrop, ha, ↓reduceDIte]
  rw [h3]
  linarith

/-- Bounded differences and a bounded sum bound the `ℓ¹` norm. -/
theorem sum_abs_le_of_sub_le {n : ℕ} (x : Fin n → ℝ) {T R : ℝ}
    (hT : ∀ i j, x i - x j ≤ T) (hR : |∑ i, x i| ≤ R) :
    ∑ i, |x i| ≤ n * (R + n * T) := by
  calc ∑ i, |x i| ≤ ∑ _i : Fin n, (R + n * T) :=
        Finset.sum_le_sum fun i _ => abs_le_of_sub_le x hT hR i
    _ = n * (R + n * T) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The two regimes of the chamber.** A chamber vector with bounded sum either has bounded
`ℓ¹` norm, or has a block position `a` across which all gaps are at most `-ℓ ≤ 0`, where `ℓ`
controls the `ℓ¹` norm linearly. -/
theorem chamber_alternative {n : ℕ} {K R : ℝ} (hK : 0 ≤ K) (x : Fin n → ℝ) (hx : Chamber K x)
    (hR : |∑ i, x i| ≤ R) :
    ∑ i, |x i| ≤ n * (R + n * (n * (K + 2 * n * K))) ∨
      ∃ a : Fin n, 0 < a.val ∧ ∃ ℓ : ℝ, 0 ≤ ℓ ∧
        (∀ i j : Fin n, i.val < a.val → a.val ≤ j.val → x j - x i ≤ -ℓ) ∧
        ∑ i, |x i| ≤ n * (R + n * (n * (K + 2 * n * K))) + (n : ℝ) ^ 3 * ℓ := by
  have hm : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hT : (0 : ℝ) ≤ 2 * n * K := by positivity
  by_cases hcase : ∀ a : Fin n, 0 < a.val → chamberDrop x a ≤ 2 * n * K
  · left
    have hdrop : ∀ i j : Fin n, i.val + 1 = j.val → x i - x j ≤ 2 * n * K := fun i j hij => by
      rw [← chamberDrop_of_succ x i j hij]
      exact hcase j (by omega)
    exact sum_abs_le_of_sub_le x (sub_le_of_chamber hK hT x hx hdrop) hR
  · right
    simp only [not_forall, not_le] at hcase
    obtain ⟨a₀, ha₀, hT₀⟩ := hcase
    obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image
      (Finset.univ.filter fun a : Fin n => 0 < a.val) (chamberDrop x)
      ⟨a₀, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ha₀⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hmax
    have hDT : 2 * n * K < chamberDrop x a := hT₀.trans_le (hmax a₀ ha₀)
    refine ⟨a, ha, chamberDrop x a - 2 * n * K, by linarith, fun i j hi hj => ?_, ?_⟩
    · have := gap_le_of_chamber hK x hx a ha i j hi hj
      linarith
    · have hdrop : ∀ i j : Fin n, i.val + 1 = j.val → x i - x j ≤ chamberDrop x a :=
        fun i j hij => by
          rw [← chamberDrop_of_succ x i j hij]
          exact hmax j (by omega)
      have h := sum_abs_le_of_sub_le x (sub_le_of_chamber hK (hT.trans hDT.le) x hx hdrop) hR
      have heq : (n : ℝ) * (R + n * (n * (K + chamberDrop x a))) =
          n * (R + n * (n * (K + 2 * n * K))) + (n : ℝ) ^ 3 * (chamberDrop x a - 2 * n * K) := by
        ring
      linarith

/-- The exponent bookkeeping of `exists_chamber_decay`. -/
theorem decay_exponent_le {c c₀ d B₀ ℓ s m N : ℝ} (hcd : 0 ≤ c + d * c₀) (hℓ : 0 ≤ ℓ)
    (hs : s ≤ B₀ + m * ℓ) (hN : m * (c + d * c₀) ≤ N) :
    -(N * ℓ) + d * (c₀ * s) ≤ (c + d * c₀) * B₀ + -(c * s) := by
  have h3 := mul_le_mul_of_nonneg_left hs hcd
  have h4 := mul_le_mul_of_nonneg_right hN hℓ
  nlinarith

end Langlands.Automorphic.CuspidalL2

namespace Langlands.Automorphic.OperatorRealization

open Langlands.Global Langlands.Automorphic.CuspidalL2 ContinuousRationalFunctions

variable {F : Type u} [Field F] [NumberField F] {n : ℕ} (S : OperatorRealization F n)

/-- Polynomial growth of a realized vector on torus translates of a compact set. -/
theorem exists_torus_growth (f : S.Space) (Q : Set (AdelicGL F n)) (hQ : IsCompact Q) :
    ∃ (d : ℕ) (C : ℝ), ∀ x, ∀ q ∈ Q,
      ‖evaluate F n (S.toContinuous f) (AdelicGL.ofInfinite F n (torInf F n x) * q)‖ ≤
        C * ArchimedeanGL.matrixHeight F n (torInf F n x) ^ d := by
  refine (S.exists_level f).elim fun L hL => ?_
  refine (S.exists_uniform_growth f L hL.1 hL.2 Q hQ).elim fun d hd => ?_
  refine hd.elim fun F₀ hF₀ => ?_
  refine (hF₀.2 1 Q hQ hF₀.1).elim fun C hC => ⟨d, C, fun x q hq => ?_⟩
  have := hC x q hq
  simpa only [map_one, Module.End.one_apply] using this

/-- **Exponential decay on the chamber.** On torus translates `torInf x * q` of a compact set,
with `x` in a chamber and of bounded sum, a vector of a cuspidal operator realization decays
faster than `exp (-c ∑ |x i|)` for every `c ≥ 0`. -/
theorem exists_chamber_decay [CompactSpace (AdeleQuotient F)] (hS : S.IsCuspidal) (f : S.Space)
    (Q : Set (AdelicGL F n)) (hQ : IsCompact Q) {K R c : ℝ} (hK : 0 ≤ K) (hc : 0 ≤ c) :
    ∃ C : ℝ, ∀ x : Fin n → ℝ, Chamber K x → |∑ i, x i| ≤ R → ∀ q ∈ Q,
      ‖evaluate F n (S.toContinuous f) (AdelicGL.ofInfinite F n (torInf F n x) * q)‖ ≤
        C * Real.exp (-(c * ∑ i, |x i|)) := by
  refine (exists_matrixHeight_torInf_le F n).elim fun C₀ h₀ => ?_
  refine h₀.elim fun c₀ ⟨hC₀, hc₀, hH⟩ => ?_
  refine (S.exists_torus_growth f Q hQ).elim fun d₁ h₁ => ?_
  refine h₁.elim fun C₁ hC₁ => ?_
  refine (S.exists_blockDecay hS f Q hQ).elim fun d₂ hdecay => ?_
  set B₀ : ℝ := n * (R + n * (n * (K + 2 * n * K))) with hB₀
  set N : ℕ := ⌈(n : ℝ) ^ 3 * (c + d₂ * c₀)⌉₊ with hN
  have hblock : ∀ a : Fin n, ∃ Cb : ℝ, 0 < a.val → ∀ (x : Fin n → ℝ) (ℓ : ℝ), 0 ≤ ℓ →
      (∀ i j : Fin n, i.val < a.val → a.val ≤ j.val → x j - x i ≤ -ℓ) → ∀ q ∈ Q,
        ‖evaluate F n (S.toContinuous f) (AdelicGL.ofInfinite F n (torInf F n x) * q)‖ ≤
          Cb * Real.exp (-(N * ℓ)) * ArchimedeanGL.matrixHeight F n (torInf F n x) ^ d₂ := by
    intro a
    by_cases ha : 0 < a.val
    · have h : a.val + (n - a.val) = n := Nat.add_sub_cancel' a.isLt.le
      refine (hdecay h ha (by omega) N).elim fun Cb hCb => ?_
      refine ⟨Cb, fun _ x ℓ hℓ hx q hq => hCb x ℓ hℓ (fun p r => hx _ _ ?_ ?_) q hq⟩
      · simp
      · simp
    · exact ⟨0, fun h => absurd h ha⟩
  choose Cb hCb using hblock
  have hCg : 0 ≤ |C₁| * (C₀ * Real.exp (c₀ * B₀)) ^ d₁ * Real.exp (c * B₀) := by positivity
  have hCd : 0 ≤ (∑ a, |Cb a|) * C₀ ^ d₂ * Real.exp ((c + d₂ * c₀) * B₀) := by positivity
  refine ⟨|C₁| * (C₀ * Real.exp (c₀ * B₀)) ^ d₁ * Real.exp (c * B₀) +
    (∑ a, |Cb a|) * C₀ ^ d₂ * Real.exp ((c + d₂ * c₀) * B₀), fun x hx hR q hq => ?_⟩
  have hsum0 : 0 ≤ ∑ i, |x i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hH1 : 1 ≤ ArchimedeanGL.matrixHeight F n (torInf F n x) :=
    ArchimedeanGL.one_le_matrixHeight F n _
  have hH0 : 0 ≤ ArchimedeanGL.matrixHeight F n (torInf F n x) := zero_le_one.trans hH1
  have hexp0 : 0 < Real.exp (-(c * ∑ i, |x i|)) := Real.exp_pos _
  rcases chamber_alternative hK x hx hR with h1 | ⟨a, ha, ℓ, hℓ, hgap, h2⟩
  · have hHB : ArchimedeanGL.matrixHeight F n (torInf F n x) ≤ C₀ * Real.exp (c₀ * B₀) :=
      (hH x).trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h1 hc₀)) hC₀)
    have hlow : 1 ≤ Real.exp (c * B₀) * Real.exp (-(c * ∑ i, |x i|)) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith)
    calc _ ≤ C₁ * ArchimedeanGL.matrixHeight F n (torInf F n x) ^ d₁ := hC₁ x q hq
      _ ≤ |C₁| * ArchimedeanGL.matrixHeight F n (torInf F n x) ^ d₁ :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hH0 _)
      _ ≤ |C₁| * (C₀ * Real.exp (c₀ * B₀)) ^ d₁ :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hH0 hHB _) (abs_nonneg _)
      _ ≤ |C₁| * (C₀ * Real.exp (c₀ * B₀)) ^ d₁ *
            (Real.exp (c * B₀) * Real.exp (-(c * ∑ i, |x i|))) :=
          le_mul_of_one_le_right (by positivity) hlow
      _ = |C₁| * (C₀ * Real.exp (c₀ * B₀)) ^ d₁ * Real.exp (c * B₀) *
            Real.exp (-(c * ∑ i, |x i|)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCd) hexp0.le
  · have hHd : ArchimedeanGL.matrixHeight F n (torInf F n x) ^ d₂ ≤
        C₀ ^ d₂ * Real.exp (d₂ * (c₀ * ∑ i, |x i|)) := by
      rw [Real.exp_nat_mul, ← mul_pow]
      exact pow_le_pow_left₀ hH0 (hH x) d₂
    have hkey : -(N * ℓ) + d₂ * (c₀ * ∑ i, |x i|) ≤
        (c + d₂ * c₀) * B₀ + -(c * ∑ i, |x i|) := by
      have hNc : (n : ℝ) ^ 3 * (c + d₂ * c₀) ≤ N := Nat.le_ceil _
      have hcd : 0 ≤ c + d₂ * c₀ := by positivity
      exact decay_exponent_le hcd hℓ h2 hNc
    have hCa : |Cb a| ≤ ∑ a, |Cb a| :=
      Finset.single_le_sum (f := fun a => |Cb a|) (fun a _ => abs_nonneg _) (Finset.mem_univ a)
    calc _ ≤ Cb a * Real.exp (-(N * ℓ)) * ArchimedeanGL.matrixHeight F n (torInf F n x) ^ d₂ :=
          hCb a ha x ℓ hℓ hgap q hq
      _ ≤ |Cb a| * Real.exp (-(N * ℓ)) *
            (C₀ ^ d₂ * Real.exp (d₂ * (c₀ * ∑ i, |x i|))) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le) hHd
            (pow_nonneg hH0 _) (by positivity)
      _ = |Cb a| * C₀ ^ d₂ * Real.exp (-(N * ℓ) + d₂ * (c₀ * ∑ i, |x i|)) := by
          rw [Real.exp_add]; ring
      _ ≤ (∑ a, |Cb a|) * C₀ ^ d₂ * Real.exp ((c + d₂ * c₀) * B₀ + -(c * ∑ i, |x i|)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hCa (pow_nonneg hC₀ _))
            (Real.exp_le_exp.mpr hkey) (Real.exp_pos _).le
            (mul_nonneg (Finset.sum_nonneg fun a _ => abs_nonneg (Cb a)) (pow_nonneg hC₀ _))
      _ = (∑ a, |Cb a|) * C₀ ^ d₂ * Real.exp ((c + d₂ * c₀) * B₀) *
            Real.exp (-(c * ∑ i, |x i|)) := by rw [Real.exp_add, ← mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCg) hexp0.le

end Langlands.Automorphic.OperatorRealization

namespace Langlands.Automorphic.CuspidalL2

open MeasureTheory

/-! ### Summation over integer lattices and compact translates -/

/-- Two-sided geometric decay on `ℤ` is summable. -/
theorem summable_exp_neg_mul_abs_int {c : ℝ} (hc : 0 < c) :
    Summable fun k : ℤ => Real.exp (-(c * |(k : ℝ)|)) := by
  have hgeo : Summable fun k : ℕ => Real.exp (-c) ^ k :=
    summable_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hc))
  have hnat : ∀ k : ℕ, Real.exp (-c) ^ k = Real.exp (-(c * |((k : ℤ) : ℝ)|)) := fun k => by
    rw [← Real.exp_nat_mul, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg k)]
    ring_nf
  have hneg : ∀ k : ℕ, Real.exp (-c) ^ k = Real.exp (-(c * |((-(k : ℤ) : ℤ) : ℝ)|)) := fun k => by
    rw [← Real.exp_nat_mul, Int.cast_neg, Int.cast_natCast, abs_neg,
      abs_of_nonneg (Nat.cast_nonneg k)]
    ring_nf
  exact Summable.of_nat_of_neg (hgeo.congr hnat) (hgeo.congr hneg)

/-- Products of a nonnegative summable function on `ℤ` are summable on `ℤ ^ n`. -/
theorem summable_prod_fin {n : ℕ} (g : ℤ → ℝ) (hg : Summable g) (hg0 : ∀ k, 0 ≤ g k) :
    Summable fun m : Fin n → ℤ => ∏ i, g (m i) := by
  induction n with
  | zero => exact Summable.of_finite
  | succ n ih =>
    refine (Equiv.summable_iff (Fin.consEquiv fun _ => ℤ)).mp ?_
    refine (hg.mul_of_nonneg ih (fun k => hg0 k)
      (fun m => Finset.prod_nonneg fun i _ => hg0 (m i))).congr fun p => ?_
    simp only [Function.comp_apply, Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ,
      Fin.cons_zero, Fin.cons_succ]

end Langlands.Automorphic.CuspidalL2

namespace Langlands.Automorphic.CuspidalL2

/-! ### Integer parts in the chamber -/

/-- Integer parts of a chamber vector of bounded sum lie in a slightly larger chamber. -/
theorem floor_chamber {n : ℕ} {K R : ℝ} (x : Fin n → ℝ) (hx : Chamber K x)
    (hR : |∑ i, x i| ≤ R) :
    Chamber (K + 1) (fun i => ((⌊x i⌋ : ℤ) : ℝ)) ∧ |∑ i, ((⌊x i⌋ : ℤ) : ℝ)| ≤ R + n := by
  constructor
  · intro i j hij
    have := hx i j hij
    have h1 := Int.floor_le (x j)
    have h2 := Int.lt_floor_add_one (x i)
    show ((⌊x j⌋ : ℤ) : ℝ) - ⌊x i⌋ ≤ K + 1
    linarith
  · have hsum : ∑ i, ((⌊x i⌋ : ℤ) : ℝ) = ∑ i, x i - ∑ i, Int.fract (x i) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => (Int.self_sub_fract (x i)).symm
    have h0 : 0 ≤ ∑ i, Int.fract (x i) := Finset.sum_nonneg fun i _ => Int.fract_nonneg _
    have h1 : ∑ i, Int.fract (x i) ≤ n := by
      calc ∑ i, Int.fract (x i) ≤ ∑ _i : Fin n, (1 : ℝ) :=
            Finset.sum_le_sum fun i _ => (Int.fract_lt_one _).le
        _ = n := by simp
    rw [hsum]
    have := abs_le.mp hR
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Shifting a chamber vector by a vector of the unit cube. -/
theorem shift_chamber {n : ℕ} {K R : ℝ} (m y : Fin n → ℝ) (hy : ∀ i, y i ∈ Set.Icc (0 : ℝ) 1)
    (hm : Chamber (K + 1) m) (hR : |∑ i, m i| ≤ R + n) :
    Chamber (K + 2) (m + y) ∧ |∑ i, (m + y) i| ≤ R + 2 * n ∧
      ∑ i, |m i| - n ≤ ∑ i, |(m + y) i| := by
  have hsum : ∑ i, (m + y) i = ∑ i, m i + ∑ i, y i := Finset.sum_add_distrib
  have h0 : 0 ≤ ∑ i, y i := Finset.sum_nonneg fun i _ => (hy i).1
  have h1 : ∑ i, y i ≤ n := by
    calc ∑ i, y i ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => (hy i).2
      _ = n := by simp
  refine ⟨fun i j hij => ?_, ?_, ?_⟩
  · have := hm i j hij
    have := hy i
    have := hy j
    show m j + y j - (m i + y i) ≤ K + 2
    linarith [(hy i).1, (hy j).2]
  · rw [hsum]
    have := abs_le.mp hR
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · have hle : ∀ i, |m i| ≤ |(m + y) i| + 1 := fun i => by
      have h := abs_sub_abs_le_abs_sub (m i) (-y i)
      have hy' : |(-y i)| ≤ 1 := by rw [abs_neg, abs_of_nonneg (hy i).1]; exact (hy i).2
      have h2 : m i - -y i = (m + y) i := by simp [sub_neg_eq_add]
      rw [h2] at h
      have h3 : |m i| ≤ |m i - -y i| + |(-y i)| := by
        have := abs_sub_abs_le_abs_sub (m i) (-y i)
        linarith [abs_nonneg (-y i)]
      linarith
    have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hle i
    rw [Finset.sum_add_distrib] at this
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      at this
    linarith

/-- Squared exponential lattice bounds are summable over any set of integer vectors. -/
theorem summable_sq_lattice_bound {n : ℕ} (P : (Fin n → ℤ) → Prop) (A : ℝ) :
    Summable fun m : {m : Fin n → ℤ // P m} =>
      (A * Real.exp (-(∑ i, |((m.1 i : ℤ) : ℝ)|))) ^ 2 := by
  have hs : Summable fun m : Fin n → ℤ => ∏ i, Real.exp (-(2 * |((m i : ℤ) : ℝ)|)) :=
    summable_prod_fin (fun k : ℤ => Real.exp (-(2 * |(k : ℝ)|)))
      (summable_exp_neg_mul_abs_int two_pos) fun k => (Real.exp_pos _).le
  refine ((hs.comp_injective Subtype.val_injective).mul_left (A ^ 2)).congr fun m => ?_
  have hexp : ∏ i, Real.exp (-(2 * |((m.1 i : ℤ) : ℝ)|)) =
      Real.exp (-(∑ i, |((m.1 i : ℤ) : ℝ)|)) ^ 2 := by
    rw [← Real.exp_sum, ← Real.exp_nat_mul]
    congr 1
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
    push_cast
    ring
  simp only [Function.comp_apply]
  rw [hexp, mul_pow]

end Langlands.Automorphic.CuspidalL2

namespace Langlands.Global

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

/-- The adelic general linear group is Hausdorff. -/
theorem adelicGL_t2Space : T2Space (AdelicGL F n) := by
  have : T2Space (InfiniteAdeleRing F) :=
    inferInstanceAs (T2Space ((v : NumberField.InfinitePlace F) → v.Completion))
  have : T2Space (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (Πʳ v : FinitePlace F,
      [FiniteCompletion F v, v.adicCompletionIntegers F]))
  have : T2Space (AdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (InfiniteAdeleRing F × IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))
  infer_instance

/-- The sum of torus coordinates is controlled by determinants. -/
theorem abs_sum_le_of_absDet (x : Fin n → ℝ) (q : AdelicGL F n) :
    |∑ i, x i| ≤ |Real.log (absDet F n (AdelicGL.ofInfinite F n (torInf F n x) * q))| +
      |Real.log (absDet F n q)| := by
  have hd : (1 : ℝ) ≤ Module.finrank ℚ F := Nat.one_le_cast.mpr Module.finrank_pos
  have h : Real.log (absDet F n (AdelicGL.ofInfinite F n (torInf F n x) * q)) =
      Module.finrank ℚ F * ∑ i, x i + Real.log (absDet F n q) := by
    rw [absDet_mul, absDet_ofInfinite_torInf,
      Real.log_mul (pow_pos (Real.exp_pos _) _).ne' (absDet_pos F n q).ne', Real.log_pow,
      Real.log_exp]
  have h2 : |∑ i, x i| ≤ |(Module.finrank ℚ F : ℝ) * ∑ i, x i| := by
    rw [abs_mul, Nat.abs_cast]
    exact le_mul_of_one_le_left (abs_nonneg _) hd
  set A := Real.log (absDet F n (AdelicGL.ofInfinite F n (torInf F n x) * q))
  set B := Real.log (absDet F n q)
  have h3 : (Module.finrank ℚ F : ℝ) * ∑ i, x i = A - B := by rw [h]; ring
  rw [h3] at h2
  exact h2.trans (abs_le.mpr ⟨by linarith [neg_abs_le A, le_abs_self B],
    by linarith [le_abs_self A, neg_abs_le B]⟩)

end Langlands.Global

namespace Langlands.Automorphic.OperatorRealization

open Langlands.Global Langlands.Automorphic.CuspidalL2 ContinuousRationalFunctions MeasureTheory

variable {F : Type u} [Field F] [NumberField F] {n : ℕ} (S : OperatorRealization F n)

/-- Pointwise bound on a lattice translate of the compact piece. -/
theorem norm_le_on_lattice_translate {Q₁ : Set (AdelicGL F n)} {K R C : ℝ} (f : S.Space)
    (hC : ∀ x : Fin n → ℝ, Chamber (K + 2) x → |∑ i, x i| ≤ R + 2 * n → ∀ q ∈ Q₁,
      ‖evaluate F n (S.toContinuous f) (AdelicGL.ofInfinite F n (torInf F n x) * q)‖ ≤
        C * Real.exp (-(1 * ∑ i, |x i|)))
    (m y : Fin n → ℝ) (hy : ∀ i, y i ∈ Set.Icc (0 : ℝ) 1) (hm : Chamber (K + 1) m)
    (hR : |∑ i, m i| ≤ R + n) (q : AdelicGL F n) (hq : q ∈ Q₁) :
    ‖evaluate F n (S.toContinuous f) (AdelicGL.ofInfinite F n (torInf F n m) *
        (AdelicGL.ofInfinite F n (torInf F n y) * q))‖ ≤
      |C| * Real.exp n * Real.exp (-(∑ i, |m i|)) := by
  obtain ⟨hz1, hz2, hz3⟩ := shift_chamber m y hy hm hR
  have heq : AdelicGL.ofInfinite F n (torInf F n m) *
      (AdelicGL.ofInfinite F n (torInf F n y) * q) =
      AdelicGL.ofInfinite F n (torInf F n (m + y)) * q := by
    rw [← mul_assoc, ← map_mul, ← torInf_add]
  have hb := hC (m + y) hz1 hz2 q hq
  have hexp : Real.exp (-(1 * ∑ i, |(m + y) i|)) ≤ Real.exp n * Real.exp (-(∑ i, |m i|)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  calc _ = ‖evaluate F n (S.toContinuous f) (AdelicGL.ofInfinite F n (torInf F n (m + y)) * q)‖ :=
        congrArg (fun g => ‖evaluate F n (S.toContinuous f) g‖) heq
    _ ≤ C * Real.exp (-(1 * ∑ i, |(m + y) i|)) := hb
    _ ≤ |C| * Real.exp (-(1 * ∑ i, |(m + y) i|)) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
    _ ≤ |C| * (Real.exp n * Real.exp (-(∑ i, |m i|))) :=
        mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
    _ = _ := (mul_assoc _ _ _).symm

variable [MeasurableSpace (AdelicGL F n)] [BorelSpace (AdelicGL F n)]

/-- **Square integrability on a determinant band.** For a cuspidal operator realization and
`0 < lo`, there is one measurable set `t` meeting the rational orbit of every adelic matrix
whose determinant has idelic absolute value in `[lo, hi]`, such that every realized vector has
finite squared integral over `t` for every left-invariant measure finite on compact sets. -/
theorem exists_band_cover [CompactSpace (AdeleQuotient F)] (hS : S.IsCuspidal) {lo hi : ℝ}
    (hlo : 0 < lo) :
    ∃ t : Set (AdelicGL F n), MeasurableSet t ∧
      (∀ g : AdelicGL F n, lo ≤ absDet F n g → absDet F n g ≤ hi →
        ∃ γ : RationalGL F n, AdelicGL.rational F n γ * g ∈ t) ∧
      ∀ (μ : Measure (AdelicGL F n)) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]
        (f : S.Space), (∫⁻ x in t, ‖evaluate F n (S.toContinuous f) x‖ₑ ^ 2 ∂μ) < ⊤ := by
  have := adelicGL_t2Space F n
  obtain ⟨Q₁, K, hQ₁, hK, hdec⟩ := exists_siegelDecomposition F n
  obtain ⟨L, hL⟩ : ∃ L : ℝ, ∀ q ∈ Q₁, |Real.log (absDet F n q)| ≤ L :=
    (hQ₁.image (continuous_abs.comp ((continuous_absDet F n).log
      fun g => (absDet_pos F n g).ne'))).bddAbove.elim
      fun L hL => ⟨L, fun q hq => hL ⟨q, hq, rfl⟩⟩
  set R₀ : ℝ := max |Real.log lo| |Real.log hi| + L with hR₀
  set Q₂ : Set (AdelicGL F n) := (fun p : (Fin n → ℝ) × AdelicGL F n =>
    AdelicGL.ofInfinite F n (torInf F n p.1) * p.2) ''
      ((Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1) ×ˢ Q₁) with hQ₂def
  have hQ₂ : IsCompact Q₂ := ((isCompact_univ_pi fun _ => isCompact_Icc).prod hQ₁).image
    (((map_continuous (AdelicGL.ofInfinite F n)).comp
      ((continuous_torInf F n).comp continuous_fst)).mul continuous_snd)
  let ι := {m : Fin n → ℤ // Chamber (K + 1) (fun i => (m i : ℝ)) ∧ |∑ i, (m i : ℝ)| ≤ R₀ + n}
  let a : ι → AdelicGL F n := fun m => AdelicGL.ofInfinite F n (torInf F n fun i => (m.1 i : ℝ))
  refine ⟨leftTranslateCover a Q₂, measurableSet_leftTranslateCover a hQ₂, ?_, ?_⟩
  · intro g hlog hhig
    obtain ⟨γ, x, q, hq, hγ, hx⟩ := hdec g
    have hRx : |∑ i, x i| ≤ R₀ := by
      have h1 := abs_sum_le_of_absDet F n x q
      rw [← hγ, absDet_rational_mul] at h1
      have hl := Real.log_le_log hlo hlog
      have hh := Real.log_le_log (absDet_pos F n g) hhig
      have h2 : |Real.log (absDet F n g)| ≤ max |Real.log lo| |Real.log hi| :=
        abs_le.mpr ⟨by linarith [neg_abs_le (Real.log lo), le_max_left |Real.log lo| |Real.log hi|],
          by linarith [le_abs_self (Real.log hi), le_max_right |Real.log lo| |Real.log hi|]⟩
      linarith [hL q hq]
    obtain ⟨hc, hs⟩ := floor_chamber x hx hRx
    have hxy : (fun i => ((⌊x i⌋ : ℤ) : ℝ)) + (fun i => Int.fract (x i)) = x :=
      funext fun i => Int.floor_add_fract (x i)
    refine ⟨γ, Set.mem_iUnion.mpr ⟨⟨fun i => ⌊x i⌋, hc, hs⟩,
      AdelicGL.ofInfinite F n (torInf F n fun i => Int.fract (x i)) * q,
      ⟨(fun i => Int.fract (x i), q),
        ⟨fun i _ => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, hq⟩, rfl⟩, ?_⟩⟩
    show AdelicGL.ofInfinite F n (torInf F n fun i => ((⌊x i⌋ : ℤ) : ℝ)) *
      (AdelicGL.ofInfinite F n (torInf F n fun i => Int.fract (x i)) * q) =
        AdelicGL.rational F n γ * g
    rw [hγ, ← mul_assoc, ← map_mul, ← torInf_add, hxy]
  · intro μ _ _ f
    refine (S.exists_chamber_decay hS f Q₁ hQ₁ (K := K + 2) (R := R₀ + 2 * n)
      (by linarith) zero_le_one).elim fun C hC => ?_
    let b : ι → ℝ≥0 := fun m =>
      ⟨|C| * Real.exp n * Real.exp (-(∑ i, |(m.1 i : ℝ)|)), by positivity⟩
    refine lintegral_enorm_sq_leftTranslateCover_lt_top μ a hQ₂ _ b ?_ ?_
    · intro m x hx
      refine hx.elim fun p hp => ?_
      have key := S.norm_le_on_lattice_translate f hC (fun i => (m.1 i : ℝ)) p.1
        (fun i => hp.1.1 i (Set.mem_univ i)) m.2.1 m.2.2 p.2 hp.1.2
      have hx' : a m * x = AdelicGL.ofInfinite F n (torInf F n fun i => (m.1 i : ℝ)) *
          (AdelicGL.ofInfinite F n (torInf F n p.1) * p.2) :=
        congrArg (fun z => a m * z) hp.2.symm
      refine NNReal.coe_le_coe.mp ?_
      calc ((‖evaluate F n (S.toContinuous f) (a m * x)‖₊ : ℝ≥0) : ℝ)
          = ‖evaluate F n (S.toContinuous f) (a m * x)‖ := coe_nnnorm _
        _ = ‖evaluate F n (S.toContinuous f)
              (AdelicGL.ofInfinite F n (torInf F n fun i => (m.1 i : ℝ)) *
                (AdelicGL.ofInfinite F n (torInf F n p.1) * p.2))‖ :=
            congrArg (fun g => ‖evaluate F n (S.toContinuous f) g‖) hx'
        _ ≤ _ := key
    · refine NNReal.summable_coe.mp
        ((summable_sq_lattice_bound _ (|C| * Real.exp n)).congr fun m => ?_)
      rw [NNReal.coe_pow]
      rfl

end Langlands.Automorphic.OperatorRealization
