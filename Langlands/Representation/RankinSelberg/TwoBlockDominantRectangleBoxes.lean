import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstRectangleSupport
import Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceCoordinates
import Langlands.Representation.RankinSelberg.TwoBlockDominantRectangleHaar
import Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergence.BoxIntegrability
import Langlands.LocalField.Normalization.Continuity

/-! # Lattice boxes for the actual dominant rectangles -/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockDominantRectangular

open GeneralLinear Whittaker HarmonicAnalysis TwoBlockDeformation TwoBlockLowerUnipotentQuotient
  TwoBlockConvergence TwoBlockLowerFixedSlice TwoBlockJacquet
open scoped BigOperators NNReal ENNReal

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance rectangleBoxesTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance rectangleBoxesValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance rectangleBoxesLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

/-- Membership in the standard lattice box is an entrywise absolute-value bound. -/
theorem mem_box_iff_normalizedAbs {a b e : ℕ}
    (x : Matrix (Fin a) (Fin b) F.Carrier) :
    x ∈ box F a b e ↔ ∀ i l, F.canonicalTopologicalData.normalizedAbs (x i l) ≤
      (F.canonicalTopologicalData.residueCardinality : ℝ) ^ e := by
  set T := F.canonicalTopologicalData
  have hq : (0 : ℝ) < T.residueCardinality := by
    exact_mod_cast (zero_lt_one.trans T.residueCardinality_gt_one)
  have hp : T.normalizedAbs ((T.uniformizer : F.Carrier) ^ e) =
      ((T.residueCardinality : ℝ) ^ e)⁻¹ := by
    simpa only [zpow_natCast, Units.val_pow_eq_pow_val,
      LocalFactor.PadicAbelian.uniformizerUnit_coe, zpow_neg] using
      LocalFactor.PadicAbelian.uniformizerUnit_zpow_abs T (e : ℤ)
  change (∀ i l, (T.uniformizer : F.Carrier) ^ e * x i l ∈ T.Integers) ↔ _
  simp only [← T.normalizedAbs_le_one_iff_mem_integers, T.normalizedAbs_mul, hp]
  constructor
  · intro hx i l
    simpa only [mul_one] using (inv_mul_le_iff₀ (pow_pos hq e)).mp (hx i l)
  · intro hx i l
    exact (inv_mul_le_iff₀ (pow_pos hq e)).mpr (by simpa only [mul_one] using hx i l)

/-- Every compact set of rectangular matrices is contained in one standard box. -/
theorem exists_box_of_isCompact {a b : ℕ}
    {C : Set (Matrix (Fin a) (Fin b) F.Carrier)} (hC : IsCompact C) :
    ∃ N : ℕ, C ⊆ box F a b N := by
  classical
  set T := F.canonicalTopologicalData
  have hq : (1 : ℝ) < T.residueCardinality := by
    exact_mod_cast T.residueCardinality_gt_one
  have hentry : ∀ i : Fin a, ∀ l : Fin b, ∃ N : ℕ,
      ∀ x ∈ C, T.normalizedAbs (x i l) ≤ (T.residueCardinality : ℝ) ^ N := by
    intro i l
    have hcont : Continuous (fun x : Matrix (Fin a) (Fin b) F.Carrier => x i l) :=
      (continuous_apply l).comp (continuous_apply i)
    obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn
      (T.continuous_normalizedAbs.comp hcont).continuousOn
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt M hq
    refine ⟨N, fun x hx => ?_⟩
    have hm := hM x hx
    simp only [Function.comp_apply, Real.norm_of_nonneg (T.normalizedAbs_nonneg _)] at hm
    exact hm.trans hN.le
  choose N hN using hentry
  refine ⟨Finset.univ.sup (fun i => Finset.univ.sup (N i)), fun x hx => ?_⟩
  rw [mem_box_iff_normalizedAbs]
  intro i l
  exact (hN i l x hx).trans (pow_le_pow_right₀ hq.le
    ((Finset.le_sup (f := N i) (Finset.mem_univ l)).trans
      (Finset.le_sup (f := fun i => Finset.univ.sup (N i)) (Finset.mem_univ i))))

/-- Multiplication adds entrywise denominator exponents, including for nonsquare matrices. -/
theorem box_mul {a b c N e : ℕ}
    {x : Matrix (Fin a) (Fin b) F.Carrier} {y : Matrix (Fin b) (Fin c) F.Carrier}
    (hx : x ∈ box F a b N) (hy : y ∈ box F b c e) :
    x * y ∈ box F a c (N + e) := by
  intro i l
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Subring.sum_mem _ fun d _ => ?_
  rw [show (F.canonicalTopologicalData.uniformizer : F.Carrier) ^ (N + e) *
      (x i d * y d l) =
      ((F.canonicalTopologicalData.uniformizer : F.Carrier) ^ N * x i d) *
        ((F.canonicalTopologicalData.uniformizer : F.Carrier) ^ e * y d l) by ring]
  exact mul_mem (hx i d) (hy d l)

/-- A bounded inverse removes a right matrix factor at the cost of its exponent. -/
theorem mem_box_of_mul_mem_box {a b N e : ℕ}
    {x : Matrix (Fin a) (Fin b) F.Carrier} {g : GeneralLinear b F.Carrier}
    (hx : x * g.val ∈ box F a b N)
    (hg : IsEntryBounded
      (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) e g) :
    x ∈ box F a b (N + e) := by
  have hgi : g⁻¹.val ∈ box F b b e := fun i l => (hg i l).2
  have hm := box_mul F hx hgi
  simpa only [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.mul_one] using hm

/-- Negation and transpose preserve the denominator exponent. -/
theorem box_neg_transpose {a b e : ℕ} {x : Matrix (Fin a) (Fin b) F.Carrier}
    (hx : -x.transpose ∈ box F b a e) : x ∈ box F a b e := by
  intro i l
  have h := neg_mem (hx l i)
  simpa only [Matrix.neg_apply, Matrix.transpose_apply, mul_neg, neg_neg] using h

/-- Row and column reversal preserve the denominator exponent. -/
theorem box_of_reverse {a b e : ℕ} {x : Matrix (Fin a) (Fin b) F.Carrier}
    (hx : x.submatrix Fin.rev Fin.rev ∈ box F a b e) : x ∈ box F a b e := by
  intro i l
  simpa only [Matrix.submatrix_apply, Fin.rev_rev] using hx i.rev l.rev

/-- Increasing the denominator exponent enlarges the box. -/
theorem box_mono {a b N M : ℕ} (hNM : N ≤ M) :
    box F a b N ⊆ box F a b M := by
  intro x hx
  rw [mem_box_iff_normalizedAbs] at hx ⊢
  have hq : (1 : ℝ) ≤ F.canonicalTopologicalData.residueCardinality := by
    exact_mod_cast F.canonicalTopologicalData.residueCardinality_gt_one.le
  exact fun i l => (hx i l).trans (pow_le_pow_right₀ hq hNM)

/-- Reversed inverse transpose preserves the common entry bound. -/
theorem isEntryBounded_reflected {a e : ℕ} {g : GeneralLinear a F.Carrier}
    (hg : IsEntryBounded
      (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) e g) :
    IsEntryBounded
      (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) e
      (weylLong a F.Carrier * inverseTranspose a F.Carrier g * weylLong a F.Carrier) := by
  intro i l
  constructor
  · simpa only [weylLong_conjugate_entry, inverseTranspose_entry] using (hg l.rev i.rev).2
  · simpa only [mul_inv_rev, weylLong_inv, ← mul_assoc, ← map_inv,
      weylLong_conjugate_entry, inverseTranspose_entry, inv_inv] using (hg l.rev i.rev).1

variable {t r j k : ℕ} {m : Fin 2 → ℕ}

/-- The actual nonzero coefficient restricts both rectangles to a common
box whose exponent is a fixed constant plus the torus size. -/
def IsTorusRectangleBoxSupport
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (ell : glFunctionals ψ r π) (W : (coefficientModel π ell).toSubmodule)
    (N : ℕ) : Prop :=
  ∀ (lam : Fin (t + 1) → ℤ) (c : GeneralLinear (t + 1) F.Carrier)
    (x : Matrix (Fin (m 0 + 1)) (Fin k) F.Carrier)
    (y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier),
    c ∈ integralOpen F t →
    W.val.val (matrix h hr (Iwasawa.torus
      (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) lam * c) x y) ≠ 0 →
    x ∈ box F (m 0 + 1) k (N + torusSize lam) ∧
      y ∈ box F j (m 1 + 1) (N + torusSize lam)

/-- Both actual rectangles have a uniform box bound, before all torus and
right integral parameters. -/
theorem exists_torus_rectangle_box_support
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hπ : IsSmooth π) (ell : glFunctionals ψ r π)
    (W : (coefficientModel π ell).toSubmodule) :
    ∃ N, IsTorusRectangleBoxSupport F ψ h hr π ell W N := by
  obtain ⟨C₀, hC₀, hs₀⟩ := exists_levi_first_rectangular_support F ψ h hr π hπ ell W
  obtain ⟨C₁, hC₁, hs₁⟩ := exists_levi_second_rectangular_support F ψ h hr π hπ ell W
  obtain ⟨N₀, hN₀⟩ := exists_box_of_isCompact F hC₀
  obtain ⟨N₁, hN₁⟩ := exists_box_of_isCompact F hC₁
  refine ⟨max N₀ N₁, fun lam c x y hc hW => ?_⟩
  have hW' :
      W.val.val (matrix h hr
        ((succBlockShape m h).leviEmbedding F.Carrier (torusLevi F h lam) * c) x y) ≠ 0 := by
    simpa only [torusLevi_embedding] using hW
  have hx := mem_box_of_mul_mem_box F
    (hN₀ (hs₀ (torusLevi F h lam) c x y hc hW'))
    (isEntryBounded_reflected F (torusLevi_entryBounded F h lam 0))
  have hy := mem_box_of_mul_mem_box F
    (hN₁ (hs₁ (torusLevi F h lam) c x y hc hW'))
    (torusLevi_entryBounded F h lam 1)
  exact ⟨box_mono F (Nat.add_le_add_right (le_max_left _ _) _) (box_neg_transpose F hx),
    box_mono F (Nat.add_le_add_right (le_max_right _ _) _) (box_of_reverse F hy)⟩

local instance rectangleBoxesMeasurable : MeasurableSpace F.Carrier := borel _
local instance rectangleBoxesBorel : BorelSpace F.Carrier := ⟨rfl⟩

/-- The common box for both actual rectangles is measurable. -/
theorem measurableSet_rectangle_box (m : Fin 2 → ℕ) (j k e : ℕ) :
    MeasurableSet ((box F (m 0 + 1) k e) ×ˢ (box F j (m 1 + 1) e)) :=
  (measurableSet_box F _ _ _).prod (measurableSet_box F _ _ _)

/-- Exact product volume; its exponent counts every entry of both actual rectangles. -/
theorem rectangleMeasure_box
    (ν : AdditiveHaarMeasure F.Carrier) [MeasureTheory.SigmaFinite ν.measure]
    (m : Fin 2 → ℕ) (j k e : ℕ) :
    rectangleMeasure F m j k ν
        ((box F (m 0 + 1) k e) ×ˢ (box F j (m 1 + 1) e)) =
      ν.measure (F.canonicalTopologicalData.Integers : Set F.Carrier) ^
          ((m 0 + 1) * k + j * (m 1 + 1)) *
        ((F.canonicalTopologicalData.residueCardinality : ℝ≥0∞) ^
          ((m 0 + 1) * k + j * (m 1 + 1))) ^ e := by
  rw [rectangleMeasure, MeasureTheory.Measure.prod_prod,
    rectangularMeasure_box, rectangularMeasure_box, pow_add, pow_add, mul_pow]
  ring

end Langlands.RankinSelberg.TwoBlockDominantRectangular
