import Langlands.Representation.Shahidi.OpenCellHaar

/-! # Integrals over columns

Fubini for a column `(y', c)` of length `n + 1`, the change of variables `y' ↦ c⁻¹ y'`, and the
integrals of an additive character of conductor `𝒪` over the lattices `ϖ^(-k) 𝒪`. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Shahidi.OpenCell

open Langlands.GeneralLinear MeasureTheory
open scoped ENNReal NNReal

universe u

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)

local instance ocColumnTopologicalSpace : TopologicalSpace K.Carrier := K.canonicalTopologicalData.topology
local instance ocColumnValuativeRel : ValuativeRel K.Carrier := K.canonicalTopologicalData.valuativeRel
local instance ocColumnIsNonarchimedeanLocalField : IsNonarchimedeanLocalField K.Carrier := K.canonicalTopologicalData.localField
local instance ocColumnTSpace : T2Space K.Carrier := K.canonicalTopologicalData.fieldT2
local instance ocColumnSecondCountableTopology : SecondCountableTopology K.Carrier :=
  K.canonicalTopologicalData.secondCountableTopology
local instance ocColumnMeasurableSpace : MeasurableSpace K.Carrier := borel K.Carrier
local instance ocColumnBorelSpace : BorelSpace K.Carrier := ⟨rfl⟩

section Column

variable (n : ℕ)

/-- A column of length `n + 1` as its last entry and the column of its first `n` entries. -/
def columnSplit : Matrix (Fin (n + 1)) (Fin 1) K.Carrier ≃ᵐ
    K.Carrier × Matrix (Fin n) (Fin 1) K.Carrier :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Fin 1 → K.Carrier) (Fin.last n)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.funUnique (Fin 1) K.Carrier)
      (MeasurableEquiv.refl _))

theorem columnSplit_apply (Y : Matrix (Fin (n + 1)) (Fin 1) K.Carrier) :
    columnSplit K n Y = (Y (Fin.last n) 0, Matrix.of fun j _ => Y j.castSucc 0) := by
  refine Prod.ext rfl ?_
  funext j k
  have hk : k = 0 := Subsingleton.elim _ _
  subst hk
  change Y ((Fin.last n).succAbove j) 0 = Y j.castSucc 0
  rw [Fin.succAbove_last_apply]

/-- The column with entries `y` followed by `c`. -/
def joinColumn (c : K.Carrier) (y : Matrix (Fin n) (Fin 1) K.Carrier) :
    Matrix (Fin (n + 1)) (Fin 1) K.Carrier :=
  Matrix.of fun i _ => Fin.lastCases c (fun j => y j 0) i

theorem columnSplit_symm (c : K.Carrier) (y : Matrix (Fin n) (Fin 1) K.Carrier) :
    (columnSplit K n).symm (c, y) = joinColumn K n c y := by
  rw [MeasurableEquiv.symm_apply_eq, columnSplit_apply]
  refine Prod.ext ?_ ?_
  · simp [joinColumn]
  · funext j k
    have hk : k = 0 := Subsingleton.elim _ _
    subst hk
    simp [joinColumn]

@[simp] theorem joinColumn_last (c : K.Carrier) (y : Matrix (Fin n) (Fin 1) K.Carrier) (k : Fin 1) :
    joinColumn K n c y (Fin.last n) k = c := by
  simp [joinColumn]

@[simp] theorem joinColumn_castSucc (c : K.Carrier) (y : Matrix (Fin n) (Fin 1) K.Carrier)
    (j : Fin n) (k : Fin 1) : joinColumn K n c y j.castSucc k = y j 0 := by
  simp [joinColumn]

theorem measurePreserving_columnSplit :
    MeasurePreserving (columnSplit K n) (matrixHaar K (n + 1) 1)
      ((haarK K).measure.prod (matrixHaar K n 1)) := by
  have h1 := measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => Measure.pi fun _ : Fin 1 => (haarK K).measure) (Fin.last n)
  have h2 := (measurePreserving_funUnique (haarK K).measure (Fin 1)).prod
    (MeasurePreserving.id (matrixHaar K n 1))
  exact h2.comp h1

/-- **Fubini over a column.** -/
theorem integral_column {G : Matrix (Fin (n + 1)) (Fin 1) K.Carrier → ℂ}
    (hG : Integrable G (matrixHaar K (n + 1) 1)) :
    ∫ Y, G Y ∂matrixHaar K (n + 1) 1 =
      ∫ c, ∫ y, G (joinColumn K n c y) ∂matrixHaar K n 1 ∂(haarK K).measure := by
  have hmp := (measurePreserving_columnSplit K n).symm
  rw [← hmp.integral_comp' G]
  have h := integral_prod _
    ((hmp.integrable_comp_emb (columnSplit K n).symm.measurableEmbedding).2 hG)
  simpa only [Function.comp_def, columnSplit_symm] using h

end Column

section Scaling

variable {a b : ℕ}

theorem smul_matrix_eq (c : K.Carrierˣ) (X : Matrix (Fin a) (Fin b) K.Carrier) :
    ((Iwasawa.diagonalUnits (fun _ : Fin a => c⁻¹) : Langlands.GeneralLinear a K.Carrier) :
      Matrix (Fin a) (Fin a) K.Carrier) * X *
        (((1 : Langlands.GeneralLinear b K.Carrier)⁻¹ : Langlands.GeneralLinear b K.Carrier) :
          Matrix (Fin b) (Fin b) K.Carrier) = ((c⁻¹ : K.Carrierˣ) : K.Carrier) • X := by
  rw [inv_one, Units.val_one, Matrix.mul_one, Iwasawa.diagonalUnits_val]
  ext i j
  simp [Matrix.diagonal_mul]

/-- **Scaling a matrix variable.** -/
theorem integral_inv_smul (c : K.Carrierˣ) (H : Matrix (Fin a) (Fin b) K.Carrier → ℂ) :
    ∫ X, H (((c⁻¹ : K.Carrierˣ) : K.Carrier) • X) ∂matrixHaar K a b =
      ((K.canonicalTopologicalData.normalizedAbs (c : K.Carrier) : ℝ) ^ (a * b) : ℝ) *
        ∫ X, H X ∂matrixHaar K a b := by
  set e : Matrix (Fin a) (Fin b) K.Carrier ≃ᵐ Matrix (Fin a) (Fin b) K.Carrier :=
    MeasurableEquiv.smul₀ ((c⁻¹ : K.Carrierˣ) : K.Carrier) (Units.ne_zero _)
  have hmap := HarmonicAnalysis.padicRectangularHaarScaling K K.canonicalTopologicalData a b
    (matrixHaar K a b) (Iwasawa.diagonalUnits (fun _ : Fin a => c⁻¹)) 1
  simp only [smul_matrix_eq] at hmap
  have he : (e : Matrix (Fin a) (Fin b) K.Carrier → Matrix (Fin a) (Fin b) K.Carrier) =
      fun X => ((c⁻¹ : K.Carrierˣ) : K.Carrier) • X := rfl
  rw [← he] at hmap
  have h := integral_map_equiv e H (μ := matrixHaar K a b)
  rw [hmap, integral_smul_nnreal_measure] at h
  change ∫ X, H (e X) ∂matrixHaar K a b = _
  rw [← h]
  have hdet : ((K.canonicalTopologicalData.determinantNorm a
      (Iwasawa.diagonalUnits fun _ : Fin a => c⁻¹) : ℝ≥0)) =
      (K.canonicalTopologicalData.normalizedAbsHom (c : K.Carrier))⁻¹ ^ a := by
    change K.canonicalTopologicalData.normalizedAbsHom
      ((Iwasawa.diagonalUnits fun _ : Fin a => c⁻¹ : Langlands.GeneralLinear a K.Carrier) :
        Matrix (Fin a) (Fin a) K.Carrier).det = _
    rw [Iwasawa.diagonalUnits_val, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, map_pow, Units.val_inv_eq_inv_val, map_inv₀]
  rw [map_one, Units.val_one, one_pow, div_one, hdet, ← pow_mul, inv_pow, inv_inv,
    NNReal.smul_def, Complex.real_smul]
  push_cast
  rfl

/-- Negation preserves the Haar measure. -/
theorem integral_neg (H : Matrix (Fin a) (Fin b) K.Carrier → ℂ) :
    ∫ X, H (-X) ∂matrixHaar K a b = ∫ X, H X ∂matrixHaar K a b := by
  have h := integral_inv_smul K (-1) H
  have h1 : K.canonicalTopologicalData.normalizedAbs (-1 : K.Carrier) = 1 := by
    have := K.canonicalTopologicalData.normalizedAbs_mul (-1) (-1)
    rw [show (-1 : K.Carrier) * (-1) = 1 by ring, K.canonicalTopologicalData.normalizedAbs_one] at this
    have hnn := K.canonicalTopologicalData.normalizedAbs_nonneg (-1 : K.Carrier)
    nlinarith
  simp only [inv_neg, inv_one, Units.val_neg, Units.val_one, neg_smul, one_smul] at h
  rw [h, h1, one_pow, Complex.ofReal_one, one_mul]

end Scaling

section Character

variable {ϖ : K.Carrierˣ} (hϖ : Iwasawa.IsUniformizingElement
    (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel) ϖ)

/-- The lattice `ϖ^(-k) 𝒪`. -/
def latticeSet (ϖ : K.Carrierˣ) (k : ℕ) : Set K.Carrier :=
  {x | (ϖ : K.Carrier) ^ k * x ∈ K.canonicalTopologicalData.Integers}

theorem latticeSet_eq_image (k : ℕ) :
    latticeSet K ϖ k = (fun x => (((ϖ ^ k)⁻¹ : K.Carrierˣ) : K.Carrier) * x) ''
      (K.canonicalTopologicalData.Integers : Set K.Carrier) := by
  ext x
  constructor
  · intro hx
    refine ⟨(ϖ : K.Carrier) ^ k * x, (hx : (ϖ : K.Carrier) ^ k * x ∈
      K.canonicalTopologicalData.Integers), ?_⟩
    simp only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ ϖ.ne_zero), one_mul]
  · rintro ⟨y, hy, rfl⟩
    show (ϖ : K.Carrier) ^ k * ((((ϖ ^ k)⁻¹ : K.Carrierˣ) : K.Carrier) * y) ∈
      K.canonicalTopologicalData.Integers
    simp only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    rwa [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ϖ.ne_zero), one_mul]

theorem isCompact_latticeSet (k : ℕ) : IsCompact (latticeSet K ϖ k) := by
  rw [latticeSet_eq_image]
  exact K.canonicalTopologicalData.isCompact_integers.image (continuous_const.mul continuous_id)

theorem measurableSet_latticeSet (k : ℕ) : MeasurableSet (latticeSet K ϖ k) :=
  (K.canonicalTopologicalData.isOpen_integers.preimage
    (continuous_const.mul continuous_id)).measurableSet

theorem latticeSet_zero : latticeSet K ϖ 0 = (K.canonicalTopologicalData.Integers : Set K.Carrier) := by
  ext x
  simp [latticeSet]

theorem latticeSet_mono {k l : ℕ} (hkl : k ≤ l) (hϖ1 : @ValuativeRel.valuation _ _
    K.canonicalTopologicalData.valuativeRel (ϖ : K.Carrier) ≤ 1) :
    latticeSet K ϖ k ⊆ latticeSet K ϖ l := by
  intro x hx
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
  have hx' : (ϖ : K.Carrier) ^ k * x ∈ K.canonicalTopologicalData.Integers := hx
  show (ϖ : K.Carrier) ^ (k + d) * x ∈ K.canonicalTopologicalData.Integers
  rw [pow_add, mul_comm ((ϖ : K.Carrier) ^ k), mul_assoc]
  exact mul_mem (pow_mem (show (ϖ : K.Carrier) ∈ K.canonicalTopologicalData.Integers from hϖ1) _) hx'

variable (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter K.Carrier _
  K.canonicalTopologicalData.topology)

theorem continuous_conj_char : Continuous fun x : K.Carrier => starRingEnd ℂ (ψ x : ℂ) :=
  Complex.continuous_conj.comp ψ.continuous_complex

theorem integrableOn_conj_char (k : ℕ) :
    IntegrableOn (fun x : K.Carrier => starRingEnd ℂ (ψ x : ℂ)) (latticeSet K ϖ k)
      (haarK K).measure :=
  (continuous_conj_char K ψ).continuousOn.integrableOn_compact (isCompact_latticeSet K k)

theorem integral_conj_char_zero (hψ : Conductor.HasIntegerConductor ψ) :
    ∫ x in latticeSet K ϖ 0, starRingEnd ℂ (ψ x : ℂ) ∂(haarK K).measure = 1 := by
  rw [latticeSet_zero]
  rw [setIntegral_congr_fun K.canonicalTopologicalData.isOpen_integers.measurableSet
    (g := fun _ => (1 : ℂ)) (fun x hx => by
      change starRingEnd ℂ (ψ x : ℂ) = 1
      rw [hψ.1 x hx]
      simp)]
  rw [setIntegral_const, measureReal_def, haarK_integers, ENNReal.toReal_one, one_smul]

include hϖ in
theorem integral_conj_char_eq_zero (hψ : Conductor.HasIntegerConductor ψ) {k : ℕ} (hk : 1 ≤ k) :
    ∫ x in latticeSet K ϖ k, starRingEnd ℂ (ψ x : ℂ) ∂(haarK K).measure = 0 := by
  set v := @ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel
  have hϖi : ((ϖ⁻¹ : K.Carrierˣ) : K.Carrier) ∉ K.canonicalTopologicalData.Integers := by
    intro h
    have h1 : v ((ϖ⁻¹ : K.Carrierˣ) : K.Carrier) ≤ 1 := h
    rw [Units.val_inv_eq_inv_val, map_inv₀] at h1
    have h2 : 1 < (v (ϖ : K.Carrier))⁻¹ := one_lt_inv_iff₀.2 ⟨Iwasawa.valuation_pos v ϖ, hϖ.1⟩
    exact absurd h1 (not_le.2 h2)
  obtain ⟨y, hy, hψy⟩ : ∃ y ∈ K.canonicalTopologicalData.Integers,
      ψ (((ϖ⁻¹ : K.Carrierˣ) : K.Carrier) * y) ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hϖi (hψ.2 _ hcon)
  set x₀ := ((ϖ⁻¹ : K.Carrierˣ) : K.Carrier) * y
  have hϖ1 : (ϖ : K.Carrier) ∈ K.canonicalTopologicalData.Integers := hϖ.1.le
  have hx₀ : x₀ ∈ latticeSet K ϖ k := by
    obtain ⟨d, rfl⟩ : ∃ d, k = d + 1 := ⟨k - 1, by omega⟩
    show (ϖ : K.Carrier) ^ (d + 1) * (((ϖ⁻¹ : K.Carrierˣ) : K.Carrier) * y) ∈
      K.canonicalTopologicalData.Integers
    rw [pow_succ, Units.val_inv_eq_inv_val, mul_assoc, ← mul_assoc (ϖ : K.Carrier),
      mul_inv_cancel₀ ϖ.ne_zero, one_mul]
    exact mul_mem (pow_mem hϖ1 d) hy
  have hadd : ∀ x, x₀ + x ∈ latticeSet K ϖ k ↔ x ∈ latticeSet K ϖ k := by
    intro x
    have hx₀' : (ϖ : K.Carrier) ^ k * x₀ ∈ K.canonicalTopologicalData.Integers := hx₀
    constructor
    · intro h
      have h' : (ϖ : K.Carrier) ^ k * (x₀ + x) ∈ K.canonicalTopologicalData.Integers := h
      show (ϖ : K.Carrier) ^ k * x ∈ K.canonicalTopologicalData.Integers
      have := sub_mem h' hx₀'
      rwa [mul_add, add_sub_cancel_left] at this
    · intro h
      have h' : (ϖ : K.Carrier) ^ k * x ∈ K.canonicalTopologicalData.Integers := h
      show (ϖ : K.Carrier) ^ k * (x₀ + x) ∈ K.canonicalTopologicalData.Integers
      rw [mul_add]
      exact add_mem hx₀' h'
  set f : K.Carrier → ℂ := fun x => starRingEnd ℂ (ψ x : ℂ)
  have hshift : ∀ x, (latticeSet K ϖ k).indicator f (x₀ + x) =
      f x₀ * (latticeSet K ϖ k).indicator f x := by
    intro x
    by_cases hx : x ∈ latticeSet K ϖ k
    · rw [Set.indicator_of_mem ((hadd x).2 hx), Set.indicator_of_mem hx]
      simp only [f, ← HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply, AddChar.map_add_eq_mul,
        map_mul]
    · rw [Set.indicator_of_notMem (fun h => hx ((hadd x).1 h)), Set.indicator_of_notMem hx,
        mul_zero]
  have hI : ∫ x in latticeSet K ϖ k, f x ∂(haarK K).measure =
      f x₀ * ∫ x in latticeSet K ϖ k, f x ∂(haarK K).measure := by
    rw [← integral_indicator (measurableSet_latticeSet K k), ← integral_const_mul]
    rw [← integral_add_left_eq_self (μ := (haarK K).measure) _ x₀]
    simp only [hshift]
  have hf₀ : f x₀ ≠ 1 := by
    intro h
    apply hψy
    have h' : (ψ x₀ : ℂ) = 1 := by
      have := congrArg (starRingEnd ℂ) h
      simpa [f] using this
    exact Circle.coe_eq_one.1 h'
  have : (1 - f x₀) * ∫ x in latticeSet K ϖ k, f x ∂(haarK K).measure = 0 := by
    rw [sub_mul, one_mul, ← hI, sub_self]
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h).symm hf₀
  · exact h

include hϖ in
theorem mem_latticeSet_iff {c : K.Carrier} {e : ℕ}
    (he : @ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel c =
      (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel (ϖ : K.Carrier)) ^
        (-(e : ℤ))) (j : ℕ) :
    c ∈ latticeSet K ϖ j ↔ e ≤ j := by
  set v := @ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel
  have hv0 : 0 < v (ϖ : K.Carrier) := Iwasawa.valuation_pos v ϖ
  have h1 : v (ϖ : K.Carrier) < 1 := hϖ.1
  change v ((ϖ : K.Carrier) ^ j * c) ≤ 1 ↔ e ≤ j
  rw [map_mul, map_pow, he, ← zpow_natCast, ← zpow_add₀ hv0.ne']
  constructor
  · intro h
    by_contra hej
    have : 1 < v (ϖ : K.Carrier) ^ ((j : ℤ) + -(e : ℤ)) :=
      one_lt_zpow_of_neg₀ hv0 h1 (by omega)
    exact absurd h (not_le.2 this)
  · intro h
    exact zpow_le_one₀ hv0 h1.le (by omega)

include hϖ in
theorem exists_valuation_eq_of_not_mem {c : K.Carrier}
    (hc : c ∉ K.canonicalTopologicalData.Integers) :
    ∃ e : ℕ, 1 ≤ e ∧ @ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel c =
      (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel (ϖ : K.Carrier)) ^
        (-(e : ℤ)) := by
  set v := @ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel
  have hc0 : c ≠ 0 := fun h => hc (h ▸ zero_mem _)
  obtain ⟨k, hk⟩ := hϖ.2 c hc0
  have hv0 : 0 < v (ϖ : K.Carrier) := Iwasawa.valuation_pos v ϖ
  have hneg : k < 0 := by
    by_contra hk0
    push Not at hk0
    apply hc
    change v c ≤ 1
    rw [hk]
    exact zpow_le_one₀ hv0 hϖ.1.le hk0
  refine ⟨(-k).toNat, by omega, ?_⟩
  rw [hk]
  congr 1
  omega

include hϖ in
/-- **The outer integral.** For `ψ` of conductor `𝒪`: if `h = C₀` on `𝒪`,
`h(c) = conj ψ(c) C_e` on `v(c) = v(ϖ)^(-e)` (`e ≥ 1`), and `C_e = 0` for `e > D`, then
`∫ h = C₀ - C₁`. -/
theorem integral_outer (hψ : Conductor.HasIntegerConductor ψ) (D : ℕ) (C : ℕ → ℂ)
    (hD : ∀ e, D < e → C e = 0) (h : K.Carrier → ℂ)
    (h0 : ∀ c ∈ K.canonicalTopologicalData.Integers, h c = C 0)
    (h1 : ∀ c, c ∉ K.canonicalTopologicalData.Integers → ∀ e : ℕ, 1 ≤ e →
      @ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel c =
        (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel (ϖ : K.Carrier)) ^
          (-(e : ℤ)) → h c = starRingEnd ℂ (ψ c : ℂ) * C e) :
    ∫ c, h c ∂(haarK K).measure = C 0 - C 1 := by
  set f : K.Carrier → ℂ := fun x => starRingEnd ℂ (ψ x : ℂ)
  set g : ℕ → K.Carrier → ℂ := fun e => (latticeSet K ϖ e).indicator f with hg
  have hϖ1 : @ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel
      (ϖ : K.Carrier) ≤ 1 := hϖ.1.le
  have hpt : ∀ c, h c = (latticeSet K ϖ 0).indicator (fun _ => C 0) c +
      ∑ e ∈ Finset.range D, (g (e + 1) c - g e c) * C (e + 1) := by
    intro c
    by_cases hc : c ∈ K.canonicalTopologicalData.Integers
    · have hc0 : c ∈ latticeSet K ϖ 0 := by rw [latticeSet_zero]; exact hc
      rw [h0 c hc, Set.indicator_of_mem hc0]
      have : ∀ e, g e c = f c := fun e =>
        Set.indicator_of_mem (latticeSet_mono K (Nat.zero_le e) hϖ1 hc0) f
      simp [this]
    · obtain ⟨e₀, he₀, hv⟩ := exists_valuation_eq_of_not_mem K hϖ hc
      have hmem : ∀ j, c ∈ latticeSet K ϖ j ↔ e₀ ≤ j := mem_latticeSet_iff K hϖ hv
      have hc0 : c ∉ latticeSet K ϖ 0 := fun h' => by
        have := (hmem 0).1 h'
        omega
      rw [Set.indicator_of_notMem hc0, zero_add, h1 c hc e₀ he₀ hv]
      have hgv : ∀ j, g j c = if e₀ ≤ j then f c else 0 := by
        intro j
        simp only [hg]
        split_ifs with hj
        · exact Set.indicator_of_mem ((hmem j).2 hj) f
        · exact Set.indicator_of_notMem (fun h' => hj ((hmem j).1 h')) f
      simp only [hgv]
      by_cases hle : e₀ ≤ D
      · rw [Finset.sum_eq_single (e₀ - 1)]
        · have he : e₀ - 1 + 1 = e₀ := by omega
          rw [he, ite_eq_left le_rfl, ite_eq_right (by omega), sub_zero]
        · intro j _ hj
          by_cases h₁ : e₀ ≤ j
          · rw [ite_eq_left (by omega), ite_eq_left h₁, sub_self, zero_mul]
          · rw [ite_eq_right (by omega), ite_eq_right h₁, sub_self, zero_mul]
        · intro hn
          exact absurd (Finset.mem_range.2 (by omega)) hn
      · rw [hD e₀ (by omega), mul_zero]
        refine (Finset.sum_eq_zero fun j hj => ?_).symm
        have hj' := Finset.mem_range.1 hj
        rw [ite_eq_right (by omega), ite_eq_right (by omega), sub_self, zero_mul]
  have hint : ∀ e, Integrable (g e) (haarK K).measure := fun e =>
    (integrable_indicator_iff (measurableSet_latticeSet K e)).2 (integrableOn_conj_char K ψ e)
  have hI : ∀ e, ∫ c, g e c ∂(haarK K).measure = if e = 0 then 1 else 0 := by
    intro e
    simp only [hg]
    rw [integral_indicator (measurableSet_latticeSet K e)]
    split_ifs with he
    · subst he
      exact integral_conj_char_zero K ψ hψ
    · exact integral_conj_char_eq_zero K hϖ ψ hψ (by omega)
  have hfin : (haarK K).measure (latticeSet K ϖ 0) < ⊤ :=
    (isCompact_latticeSet K 0).measure_lt_top
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add, integral_finsetSum]
  · rw [integral_indicator (measurableSet_latticeSet K 0), setIntegral_const, measureReal_def,
      latticeSet_zero, haarK_integers, ENNReal.toReal_one, one_smul]
    have hsum : ∀ e ∈ Finset.range D, ∫ c, (g (e + 1) c - g e c) * C (e + 1) ∂(haarK K).measure =
        (if e = 0 then -1 else 0) * C (e + 1) := by
      intro e _
      rw [integral_mul_const, integral_sub (hint _) (hint _), hI, hI]
      split_ifs <;> simp_all
    rw [Finset.sum_congr rfl hsum]
    rcases Nat.eq_zero_or_pos D with hD0 | hD0
    · subst hD0
      rw [Finset.sum_range_zero, hD 1 (by omega), sub_zero, add_zero]
    · rw [Finset.sum_eq_single 0]
      · simp only [ite_true, zero_add]
        ring
      · intro j _ hj
        rw [ite_eq_right hj, zero_mul]
      · intro hn
        exact absurd (Finset.mem_range.2 hD0) hn
  · intro e _
    exact ((hint _).sub (hint _)).mul_const _
  · exact (integrable_indicator_iff (measurableSet_latticeSet K 0)).2
      (integrableOn_const hfin.ne)
  · exact integrable_finsetSum _ fun e _ => ((hint _).sub (hint _)).mul_const _

end Character

end Langlands.Shahidi.OpenCell
