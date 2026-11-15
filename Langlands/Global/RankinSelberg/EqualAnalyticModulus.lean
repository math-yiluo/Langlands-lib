import Langlands.Global.RankinSelberg.EqualAnalyticPoisson
import Langlands.Automorphic.CuspidalL2.SiegelCover
import Langlands.Global.AdelicScalarHaarChar
import Langlands.Global.AdelesLocallyCompactProof
import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # The modulus of right multiplication on `𝔸^n`

For `g ∈ GL_n(𝔸)`, the map `x ↦ x g` of row vectors multiplies Haar measure by the idelic norm
`|det g|`. The Haar character `m(g)` of `x ↦ x g` is a homomorphism. It equals `1` on
`GL_n(F)` (the map preserves `F^n` and hence the covolume) and `|det|` on the archimedean
diagonal torus (by the product structure of the covolume-one measure). It is bounded on compact
sets. By the Siegel decomposition `γ g = t q`, the quotient `m / |det|` is a bounded
homomorphism, hence trivial.
-/

noncomputable section
universe u
open NumberField MeasureTheory Set
open scoped Classical NNReal ENNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.EqualAnalytic

open Langlands.Global Langlands.Automorphic.CuspidalWhittaker

variable (F : Type u) [Field F] [NumberField F]

local instance modulusMeasurableSpace (k m : ℕ) :
    MeasurableSpace (Matrix (Fin k) (Fin m) (Adeles F)) := borel _

local instance modulusBorelSpace (k m : ℕ) :
    BorelSpace (Matrix (Fin k) (Fin m) (Adeles F)) := ⟨rfl⟩

local instance modulusAdelesLocallyCompact : LocallyCompactSpace (Adeles F) :=
  adeles_locallyCompactSpace F

local instance modulusAdelesSecondCountable : SecondCountableTopology (Adeles F) :=
  adeles_secondCountableTopology F

local instance modulusFiniteMeasurableSpace : MeasurableSpace (FiniteAdeles F) := borel _

local instance modulusFiniteBorelSpace : BorelSpace (FiniteAdeles F) := ⟨rfl⟩

local instance modulusFiniteSecondCountable : SecondCountableTopology (FiniteAdeles F) :=
  finiteAdeles_secondCountableTopology F

local instance modulusFiniteLocallyCompact : LocallyCompactSpace (FiniteAdeles F) :=
  finiteAdeles_locallyCompactSpace F

local instance modulusRowLocallyCompact (k m : ℕ) :
    LocallyCompactSpace (Matrix (Fin k) (Fin m) (Adeles F)) :=
  inferInstanceAs (LocallyCompactSpace (Fin k → Fin m → Adeles F))

local instance modulusRowSecondCountable (k m : ℕ) :
    SecondCountableTopology (Matrix (Fin k) (Fin m) (Adeles F)) :=
  inferInstanceAs (SecondCountableTopology (Fin k → Fin m → Adeles F))

/-- Right multiplication `x ↦ x g` of row vectors by `g ∈ GL_n(𝔸)`. -/
def rightMul (n : ℕ) (g : AdelicGL F n) : RowVector F n ≃ₜ+ RowVector F n where
  toFun x := x * (g : Matrix (Fin n) (Fin n) (Adeles F))
  invFun x := x * ((g⁻¹ : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F))
  left_inv x := by
    simp only [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.mul_one]
  right_inv x := by
    simp only [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.mul_one]
  map_add' x y := Matrix.add_mul x y _
  continuous_toFun := continuous_id.matrix_mul continuous_const
  continuous_invFun := continuous_id.matrix_mul continuous_const

theorem rightMul_apply (n : ℕ) (g : AdelicGL F n) (x : RowVector F n) :
    rightMul F n g x = x * (g : Matrix (Fin n) (Fin n) (Adeles F)) := rfl

theorem rightMul_mul (n : ℕ) (g h : AdelicGL F n) :
    rightMul F n (g * h) = (rightMul F n g).trans (rightMul F n h) := by
  ext x
  simp only [rightMul_apply, ContinuousAddEquiv.trans_apply, Units.val_mul, Matrix.mul_assoc]

/-- The Haar character of `x ↦ x g`. -/
def rowModulus (n : ℕ) (g : AdelicGL F n) : ℝ≥0 := addEquivAddHaarChar (rightMul F n g)

theorem rowModulus_mul (n : ℕ) (g h : AdelicGL F n) :
    rowModulus F n (g * h) = rowModulus F n g * rowModulus F n h := by
  rw [rowModulus, rightMul_mul, addEquivAddHaarChar_trans]
  rfl

theorem rowModulus_pos (n : ℕ) (g : AdelicGL F n) : 0 < rowModulus F n g :=
  addEquivAddHaarChar_pos _

theorem rowModulus_one (n : ℕ) : rowModulus F n 1 = 1 := by
  have h := rowModulus_mul F n 1 1
  rw [mul_one] at h
  have hpos := rowModulus_pos F n 1
  have : rowModulus F n 1 * rowModulus F n 1 = rowModulus F n 1 * 1 := by rw [mul_one, ← h]
  exact mul_left_cancel₀ hpos.ne' this

theorem rowModulus_inv (n : ℕ) (g : AdelicGL F n) :
    rowModulus F n g⁻¹ = (rowModulus F n g)⁻¹ := by
  have h := rowModulus_mul F n g g⁻¹
  rw [mul_inv_cancel, rowModulus_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem rightMul_rational_ratRow (n : ℕ) (γ : RationalGL F n) (C : RatRow F n) :
    rightMul F n (AdelicGL.rational F n γ) (ratRow F n C) =
      ratRow F n (C * (γ : Matrix (Fin n) (Fin n) F)) := by
  rw [rightMul_apply]
  ext i j
  simp only [ratRow, Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul]
  rfl

/-- The preimage of the fundamental domain under `x ↦ x γ` is again a fundamental domain. -/
theorem isAddFundamentalDomain_preimage_rightMul (n : ℕ) (γ : RationalGL F n)
    (mu : Measure (RowVector F n)) :
    IsAddFundamentalDomain (rowLattice F n)
      (rightMul F n (AdelicGL.rational F n γ) ⁻¹' rowDomain F n) mu := by
  set φ := rightMul F n (AdelicGL.rational F n γ)
  apply IsAddFundamentalDomain.mk'
    ((measurableSet_rowDomain F n).preimage φ.continuous.measurable).nullMeasurableSet
  intro v
  obtain ⟨⟨μ', hμ'⟩, hμD, hμu⟩ := existsUnique_add_mem_rowDomain F n (φ v)
  obtain ⟨C, rfl⟩ := hμ'
  -- the lattice point `C γ⁻¹`
  let C' : RatRow F n := C * ((γ⁻¹ : RationalGL F n) : Matrix (Fin n) (Fin n) F)
  have hC' : φ (ratRow F n C') = ratRow F n C := by
    rw [rightMul_rational_ratRow, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.mul_one]
  refine ⟨⟨ratRow F n C', ⟨C', rfl⟩⟩, ?_, ?_⟩
  · change φ (ratRow F n C' + v) ∈ rowDomain F n
    rw [map_add, hC']
    exact hμD
  · rintro ⟨w, ⟨D, rfl⟩⟩ hw
    change φ (ratRow F n D + v) ∈ rowDomain F n at hw
    rw [map_add, rightMul_rational_ratRow] at hw
    have := hμu ⟨ratRow F n (D * (γ : Matrix (Fin n) (Fin n) F)), ⟨_, rfl⟩⟩ hw
    have hD : D * (γ : Matrix (Fin n) (Fin n) F) = C := by
      have h1 := congrArg Subtype.val this
      exact ratRow_injective F n h1
    apply Subtype.ext
    change ratRow F n D = ratRow F n (C * ((γ⁻¹ : RationalGL F n) : Matrix (Fin n) (Fin n) F))
    congr 1
    rw [← hD, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.mul_one]

variable [CompactSpace (AdeleQuotient F)]

/-- `x ↦ x γ` preserves the covolume-one measure for `γ ∈ GL_n(F)`. -/
theorem rowModulus_rational (n : ℕ) (γ : RationalGL F n) :
    rowModulus F n (AdelicGL.rational F n γ) = 1 := by
  have h := addEquivAddHaarChar_smul_preimage (rectangleMeasure F 1 n)
    (X := rowDomain F n) (rightMul F n (AdelicGL.rational F n γ))
  have h1 : rectangleMeasure F 1 n
      (rightMul F n (AdelicGL.rational F n γ) ⁻¹' rowDomain F n) = 1 := by
    rw [(isAddFundamentalDomain_preimage_rightMul F n γ (rectangleMeasure F 1 n)).measure_eq
      (isAddFundamentalDomain_rowDomain F n _)]
    exact rectangleMeasure_rowDomain F n
  rw [h1, rectangleMeasure_rowDomain, ENNReal.smul_def, smul_eq_mul, mul_one] at h
  exact_mod_cast h

/-- Coordinatewise real scaling `(y_j) ↦ (e^{x_j} y_j)` of `(F_∞)^n`. -/
def scaleRow (n : ℕ) (x : Fin n → ℝ) : ArchRow F n →ₗ[ℝ] ArchRow F n :=
  LinearMap.pi fun j => (Real.exp (x j) • LinearMap.id).comp (LinearMap.proj j)

omit [NumberField F] [CompactSpace (AdeleQuotient F)] in
theorem scaleRow_apply (n : ℕ) (x : Fin n → ℝ) (y : ArchRow F n) (j : Fin n) :
    scaleRow F n x y j = Real.exp (x j) • y j := rfl

omit [CompactSpace (AdeleQuotient F)] in
theorem det_scaleRow (n : ℕ) (x : Fin n → ℝ) :
    LinearMap.det (scaleRow F n x) = Real.exp (∑ j, x j) ^ Module.finrank ℚ F := by
  rw [scaleRow, LinearMap.det_pi]
  simp only [LinearMap.det_smul, LinearMap.det_id, mul_one, mixedEmbedding.finrank]
  rw [Finset.prod_pow, ← Real.exp_sum]

omit [CompactSpace (AdeleQuotient F)] in
theorem rowSplit_rightMul_torInf (n : ℕ) (x : Fin n → ℝ) (v : RowVector F n) :
    rowSplit F n (rightMul F n (AdelicGL.ofInfinite F n (torInf F n x)) v) =
      (scaleRow F n x (rowSplit F n v).1, (rowSplit F n v).2) := by
  have hv : rightMul F n (AdelicGL.ofInfinite F n (torInf F n x)) v =
      Matrix.of fun i j => v i j * realScale F (Real.exp (x j)) := by
    rw [rightMul_apply, ofInfinite_torInf_val]
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.of_apply]
  rw [hv]
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · change InfiniteAdeleRing.ringEquiv_mixedSpace F (v 0 j * realScale F (Real.exp (x j))).1 =
      Real.exp (x j) • InfiniteAdeleRing.ringEquiv_mixedSpace F (v 0 j).1
    rw [adeles_mul_fst, mul_comm]
    have h := PositiveRealIdeles.ringEquiv_mixedSpace_infinite_mul F (expUnit (x j)) (v 0 j).1
    rw [positiveRealIdeles_infinite_val] at h
    exact h
  · change (v 0 j * realScale F (Real.exp (x j))).2 = (v 0 j).2
    rw [adeles_mul_snd]
    exact mul_one _

/-- The Haar measure on `𝔸^n` transported from the product measure. -/
def splitHaar (n : ℕ) : Measure (RowVector F n) :=
  Measure.map (rowSplit F n).symm (rowProductMeasure F n)

instance splitHaar_isAddHaarMeasure (n : ℕ) : (splitHaar F n).IsAddHaarMeasure :=
  (rowSplit F n).symm.toAddEquiv.isAddHaarMeasure_map (rowProductMeasure F n)
    (rowSplit F n).symm.continuous (rowSplit F n).continuous

omit [CompactSpace (AdeleQuotient F)] in
theorem map_rightMul_torInf_splitHaar (n : ℕ) (x : Fin n → ℝ) :
    Measure.map (rightMul F n (AdelicGL.ofInfinite F n (torInf F n x))) (splitHaar F n) =
      ENNReal.ofReal |(LinearMap.det (scaleRow F n x))⁻¹| • splitHaar F n := by
  have hdet : LinearMap.det (scaleRow F n x) ≠ 0 := by
    rw [det_scaleRow]
    exact pow_ne_zero _ (Real.exp_pos _).ne'
  have hL : Measurable (scaleRow F n x) :=
    (LinearMap.continuous_of_finiteDimensional (scaleRow F n x)).measurable
  have hcomp : (rightMul F n (AdelicGL.ofInfinite F n (torInf F n x))) ∘ (rowSplit F n).symm =
      (rowSplit F n).symm ∘ Prod.map (scaleRow F n x) id := by
    funext p
    apply (rowSplit F n).injective
    simp only [Function.comp_apply, rowSplit_rightMul_torInf, ContinuousAddEquiv.apply_symm_apply]
    rfl
  have hφ : Measurable ⇑(rightMul F n (AdelicGL.ofInfinite F n (torInf F n x))) :=
    (rightMul F n (AdelicGL.ofInfinite F n (torInf F n x))).continuous.measurable
  have hs : Measurable ⇑(rowSplit F n).symm := (rowSplit F n).symm.continuous.measurable
  unfold splitHaar
  rw [Measure.map_map hφ hs, hcomp, ← Measure.map_map hs (hL.prodMap measurable_id),
    rowProductMeasure, ← Measure.map_prod_map _ _ hL measurable_id,
    Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdet, Measure.map_id,
    Measure.prod_smul_left, Measure.map_smul]
  exact hs.aemeasurable

omit [CompactSpace (AdeleQuotient F)] in
/-- On the archimedean diagonal torus, the modulus is `|det|`. -/
theorem rowModulus_torInf (n : ℕ) (x : Fin n → ℝ) :
    (rowModulus F n (AdelicGL.ofInfinite F n (torInf F n x)) : ℝ) =
      absDet F n (AdelicGL.ofInfinite F n (torInf F n x)) := by
  rw [absDet_ofInfinite_torInf]
  set φ := rightMul F n (AdelicGL.ofInfinite F n (torInf F n x))
  have h := addEquivAddHaarChar_smul_map (splitHaar F n) φ
  rw [map_rightMul_torInf_splitHaar] at h
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : RowVector F n)
  have hpos : splitHaar F n K ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hK0).ne'
  have hfin : splitHaar F n K ≠ ⊤ := hK.measure_lt_top.ne
  have hK' := congrArg (fun m : Measure (RowVector F n) => m K) h
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.smul_def] at hK'
  set c := ENNReal.ofReal |(LinearMap.det (scaleRow F n x))⁻¹|
  have h1 : ((addEquivAddHaarChar φ : ℝ≥0∞) * c) * splitHaar F n K = 1 * splitHaar F n K := by
    rw [one_mul, mul_assoc]
    exact hK'
  have h2 : (addEquivAddHaarChar φ : ℝ≥0∞) * c = 1 := by
    have := congrArg (· * (splitHaar F n K)⁻¹) h1
    simp only [mul_assoc, ENNReal.mul_inv_cancel hpos hfin, mul_one, one_mul] at this
    exact this
  have hdet : LinearMap.det (scaleRow F n x) = Real.exp (∑ i, x i) ^ Module.finrank ℚ F :=
    det_scaleRow F n x
  have hdpos : 0 < Real.exp (∑ i, x i) ^ Module.finrank ℚ F := by positivity
  have hc : c = ENNReal.ofReal (Real.exp (∑ i, x i) ^ Module.finrank ℚ F)⁻¹ := by
    simp only [c]
    rw [hdet, abs_of_pos (inv_pos.mpr hdpos)]
  rw [hc] at h2
  have h3 : (addEquivAddHaarChar φ : ℝ≥0∞) =
      ENNReal.ofReal (Real.exp (∑ i, x i) ^ Module.finrank ℚ F) := by
    rw [ENNReal.ofReal_inv_of_pos hdpos] at h2
    exact ENNReal.eq_inv_of_mul_eq_one_left h2 |>.trans (inv_inv _)
  have h4 := congrArg ENNReal.toReal h3
  rw [ENNReal.coe_toReal, ENNReal.toReal_ofReal hdpos.le] at h4
  exact h4

/-- The modulus is bounded on compact sets. -/
theorem exists_rowModulus_le (n : ℕ) {Q : Set (AdelicGL F n)} (hQ : IsCompact Q) :
    ∃ B : ℝ, ∀ q ∈ Q, (rowModulus F n q : ℝ) ≤ B := by
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : RowVector F n)
  have hcont : Continuous fun p : RowVector F n × AdelicGL F n =>
      p.1 * ((p.2 : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F)) :=
    continuous_fst.matrix_mul (Units.continuous_val.comp continuous_snd)
  set K₁ := (fun p : RowVector F n × AdelicGL F n =>
    p.1 * ((p.2 : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F))) '' (K ×ˢ Q)
  have hK₁ : IsCompact K₁ := (hK.prod hQ).image hcont
  have hpos : rectangleMeasure F 1 n K ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hK0).ne'
  have hfin : rectangleMeasure F 1 n K₁ ≠ ⊤ := hK₁.measure_lt_top.ne
  refine ⟨(rectangleMeasure F 1 n K₁).toReal / (rectangleMeasure F 1 n K).toReal,
    fun q hq => ?_⟩
  have h := addEquivAddHaarChar_smul_preimage (rectangleMeasure F 1 n) (X := K₁)
    (rightMul F n q)
  have hsub : K ⊆ rightMul F n q ⁻¹' K₁ := fun v hv => ⟨(v, q), ⟨hv, hq⟩, rfl⟩
  have hle : rectangleMeasure F 1 n K ≤ rectangleMeasure F 1 n (rightMul F n q ⁻¹' K₁) :=
    measure_mono hsub
  have hKfin : rectangleMeasure F 1 n K ≠ ⊤ := hK.measure_lt_top.ne
  have hKpos : 0 < (rectangleMeasure F 1 n K).toReal := ENNReal.toReal_pos hpos hKfin
  rw [le_div_iff₀ hKpos]
  have h' : (rowModulus F n q : ℝ≥0∞) * rectangleMeasure F 1 n K ≤ rectangleMeasure F 1 n K₁ := by
    rw [← h, ENNReal.smul_def, smul_eq_mul]
    exact mul_le_mul_right hle _
  have := ENNReal.toReal_mono hfin h'
  rwa [ENNReal.toReal_mul, ENNReal.coe_toReal] at this

omit [CompactSpace (AdeleQuotient F)] in
theorem absDet_one (n : ℕ) : absDet F n 1 = 1 := by
  have h := absDet_mul F n 1 1
  rw [mul_one] at h
  have hpos := absDet_pos F n 1
  have : absDet F n 1 * absDet F n 1 = absDet F n 1 * 1 := by rw [mul_one, ← h]
  exact mul_left_cancel₀ hpos.ne' this

omit [CompactSpace (AdeleQuotient F)] in
theorem absDet_rational (n : ℕ) (γ : RationalGL F n) : absDet F n (AdelicGL.rational F n γ) = 1 := by
  have h := absDet_rational_mul F n γ 1
  rwa [mul_one, absDet_one] at h

/-- **The modulus of `x ↦ x g` is `|det g|`.** -/
theorem rowModulus_eq_absDet (n : ℕ) (g : AdelicGL F n) :
    (rowModulus F n g : ℝ) = absDet F n g := by
  set ρ : AdelicGL F n → ℝ := fun g => (rowModulus F n g : ℝ) / absDet F n g with hρ
  have hρpos : ∀ g, 0 < ρ g := fun g =>
    div_pos (by exact_mod_cast rowModulus_pos F n g) (absDet_pos F n g)
  have hρmul : ∀ g h, ρ (g * h) = ρ g * ρ h := by
    intro g h
    simp only [hρ, rowModulus_mul, absDet_mul, NNReal.coe_mul]
    field_simp
  have hρrat : ∀ γ, ρ (AdelicGL.rational F n γ) = 1 := by
    intro γ
    simp only [hρ, rowModulus_rational, absDet_rational, NNReal.coe_one, div_one]
  have hρtor : ∀ x, ρ (AdelicGL.ofInfinite F n (torInf F n x)) = 1 := by
    intro x
    simp only [hρ, rowModulus_torInf]
    exact div_self (absDet_pos F n _).ne'
  obtain ⟨Q₁, K, hQ, -, hdec⟩ := exists_siegelDecomposition F n
  obtain ⟨B, hB⟩ := exists_rowModulus_le F n hQ
  obtain ⟨M, hM⟩ := hQ.exists_bound_of_continuousOn
    (((continuous_absDet F n).inv₀ fun g => (absDet_pos F n g).ne').continuousOn)
  have hbound : ∀ g, ρ g ≤ B * M := by
    intro g
    obtain ⟨γ, x, q, hq, hgq, -⟩ := hdec g
    have h1 : ρ g = ρ q := by
      have := congrArg ρ hgq
      rw [hρmul, hρmul, hρrat, hρtor, one_mul, one_mul] at this
      exact this
    rw [h1]
    have hM' := hM q hq
    rw [Real.norm_eq_abs, Pi.inv_apply, abs_of_pos (inv_pos.mpr (absDet_pos F n q))] at hM'
    have hB' := hB q hq
    calc ρ q = (rowModulus F n q : ℝ) * (absDet F n q)⁻¹ := div_eq_mul_inv _ _
      _ ≤ B * M := mul_le_mul hB' hM' (inv_pos.mpr (absDet_pos F n q)).le
          (le_trans (NNReal.coe_nonneg _) hB')
  have hle : ∀ g, ρ g ≤ 1 := by
    intro g
    have hpow : ∀ k : ℕ, ρ (g ^ k) = ρ g ^ k := by
      intro k
      induction k with
      | zero => simp [hρ, rowModulus_one, absDet_one]
      | succ k ih => rw [pow_succ, hρmul, ih, pow_succ]
    by_contra hlt
    push Not at hlt
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (B * M) hlt
    rw [← hpow k] at hk
    exact absurd (hbound (g ^ k)) (not_le.mpr hk)
  have hinv : ρ g * ρ g⁻¹ = 1 := by
    rw [← hρmul, mul_inv_cancel]
    simp [hρ, rowModulus_one, absDet_one]
  have h1 : ρ g = 1 := by
    have hg := hle g
    have hg' := hle g⁻¹
    have hp := hρpos g
    have hp' := hρpos g⁻¹
    nlinarith
  have := h1
  simp only [hρ] at this
  rwa [div_eq_one_iff_eq (absDet_pos F n g).ne'] at this

/-- **Change of variables** `x ↦ x g` on `𝔸^n`. -/
theorem map_rightMul_rectangleMeasure (n : ℕ) (g : AdelicGL F n) :
    Measure.map (rightMul F n g) (rectangleMeasure F 1 n) =
      ENNReal.ofReal (absDet F n g)⁻¹ • rectangleMeasure F 1 n := by
  have h := addEquivAddHaarChar_smul_map (rectangleMeasure F 1 n) (rightMul F n g)
  have hpos := rowModulus_pos F n g
  have hval : (rowModulus F n g : ℝ≥0∞) = ENNReal.ofReal (absDet F n g) := by
    rw [← rowModulus_eq_absDet, ENNReal.ofReal_coe_nnreal]
  have hne : (rowModulus F n g : ℝ≥0∞) ≠ 0 := by exact_mod_cast hpos.ne'
  calc Measure.map (rightMul F n g) (rectangleMeasure F 1 n) =
      (rowModulus F n g : ℝ≥0∞)⁻¹ • ((rowModulus F n g : ℝ≥0∞) •
        Measure.map (rightMul F n g) (rectangleMeasure F 1 n)) := by
        rw [smul_smul, ENNReal.inv_mul_cancel hne ENNReal.coe_ne_top, one_smul]
    _ = (rowModulus F n g : ℝ≥0∞)⁻¹ • rectangleMeasure F 1 n := by
        rw [← ENNReal.smul_def]
        change (rowModulus F n g : ℝ≥0∞)⁻¹ • (addEquivAddHaarChar (rightMul F n g) •
          Measure.map (rightMul F n g) (rectangleMeasure F 1 n)) = _
        rw [h]
    _ = ENNReal.ofReal (absDet F n g)⁻¹ • rectangleMeasure F 1 n := by
        rw [hval, ENNReal.ofReal_inv_of_pos (absDet_pos F n g)]

theorem integral_comp_rightMul (n : ℕ) (g : AdelicGL F n) (f : RowVector F n → ℂ) :
    ∫ x, f (x * (g : Matrix (Fin n) (Fin n) (Adeles F))) ∂rectangleMeasure F 1 n =
      ((absDet F n g)⁻¹ : ℝ) • ∫ x, f x ∂rectangleMeasure F 1 n := by
  have he : MeasurableEmbedding ⇑(rightMul F n g) :=
    (rightMul F n g).toHomeomorph.measurableEmbedding
  change ∫ x, f (rightMul F n g x) ∂rectangleMeasure F 1 n = _
  rw [← he.integral_map]
  change ∫ x, f x ∂(Measure.map (rightMul F n g) (rectangleMeasure F 1 n)) = _
  rw [map_rightMul_rectangleMeasure, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_pos.mpr (absDet_pos F n g)).le]

theorem integrable_comp_rightMul_iff (n : ℕ) (g : AdelicGL F n) (f : RowVector F n → ℂ) :
    Integrable (fun x => f (x * (g : Matrix (Fin n) (Fin n) (Adeles F))))
        (rectangleMeasure F 1 n) ↔ Integrable f (rectangleMeasure F 1 n) := by
  have he : MeasurableEmbedding ⇑(rightMul F n g) :=
    (rightMul F n g).toHomeomorph.measurableEmbedding
  change Integrable (f ∘ rightMul F n g) _ ↔ _
  rw [← he.integrable_map_iff]
  change Integrable f (Measure.map (rightMul F n g) (rectangleMeasure F 1 n)) ↔ _
  rw [map_rightMul_rectangleMeasure]
  exact integrable_smul_measure
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (absDet_pos F n g))).ne' ENNReal.ofReal_ne_top

end Langlands.Global.RankinSelbergGlobal.EqualAnalytic
