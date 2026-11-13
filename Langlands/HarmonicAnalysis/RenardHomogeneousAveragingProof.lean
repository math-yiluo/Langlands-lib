import Langlands.HarmonicAnalysis.RenardHomogeneousQuotientProof
import Langlands.HarmonicAnalysis.Distribution.RenardHaarLeftProof
import Langlands.HarmonicAnalysis.Distribution.RenardHaarConsequencesProof
import Langlands.HarmonicAnalysis.Distribution.RenardHaarDensityProof
import Langlands.Representation.Hecke.RenardTestDecompositionProof

/-! # Renard II.3.9: the subgroup averaging map and the invariant functional -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false

open MeasureTheory
open Langlands.Induction (LeftQuotient quotientMap)
open scoped Pointwise NNReal ComplexOrder

namespace Langlands.HarmonicAnalysis.HomogeneousFunctions.Renard

universe uG

/-! ## The modular weight -/

section Weight

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

/-- The weight `g ↦ δ_G(g)⁻¹` of the averaging integral. -/
def modularWeight (g : G) : ℂ := (((Distribution.renardModular g : ℝ)⁻¹ : ℝ) : ℂ)

theorem renardModular_pos (g : G) : 0 < Distribution.renardModular g :=
  (Distribution.RenardModular.regularity G).1 g

theorem modularWeight_mul (a b : G) :
    modularWeight (a * b) = modularWeight a * modularWeight b := by
  simp only [modularWeight, map_mul, NNReal.coe_mul, mul_inv, Complex.ofReal_mul]

theorem modularWeight_mul_modular (g : G) :
    modularWeight g * ((Distribution.renardModular g : ℝ) : ℂ) = 1 := by
  have h : ((Distribution.renardModular g : ℝ)) ≠ 0 := by
    exact_mod_cast (renardModular_pos g).ne'
  simp only [modularWeight, ← Complex.ofReal_mul, inv_mul_cancel₀ h, Complex.ofReal_one]

theorem modularWeight_eq_inv (g : G) :
    modularWeight g = ((Distribution.renardModular g⁻¹ : ℝ) : ℂ) := by
  simp only [modularWeight, map_inv, NNReal.coe_inv]

theorem modularWeight_eq_inv_cast (g : G) :
    modularWeight g = ((Distribution.renardModular g : ℝ) : ℂ)⁻¹ :=
  Complex.ofReal_inv _

theorem modularWeight_one : modularWeight (1 : G) = 1 := by
  simp only [modularWeight, map_one, NNReal.coe_one, inv_one, Complex.ofReal_one]

theorem modularWeight_mul_inv (g : G) : modularWeight g * modularWeight g⁻¹ = 1 := by
  rw [← modularWeight_mul, mul_inv_cancel, modularWeight_one]

theorem modularWeight_nonneg (g : G) : 0 ≤ modularWeight g :=
  Complex.zero_le_real.mpr (inv_nonneg.mpr (NNReal.coe_nonneg _))

theorem modularWeight_isLocallyConstant : IsLocallyConstant (modularWeight (G := G)) :=
  (Distribution.RenardModular.regularity G).2.1.comp
    (fun r : ℝ≥0 => (((r : ℝ)⁻¹ : ℝ) : ℂ))

theorem exists_right_stabilizer_test (f : SchwartzBruhat G) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ ∀ (k : K) (x : G), f (x * k) = f x := by
  obtain ⟨K, -, hK, hf⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G {f} ⊤
  exact ⟨K, hK, fun k x => (hf f (Finset.mem_singleton_self f)).2 k x⟩

end Weight

theorem complex_nonneg_iff (z : ℂ) : 0 ≤ z ↔ z.im = 0 ∧ 0 ≤ z.re := by
  rw [Complex.nonneg_iff]
  exact ⟨fun h => ⟨h.2.symm, h.1⟩, fun h => ⟨h.2, h.1.symm⟩⟩

/-! ## Weighted slices and the averaging map -/

section Averaging

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
variable {H : Subgroup G} (hH : IsClosed (H : Set G))
include hH

theorem isClosedEmbedding_slice (y : G) :
    Topology.IsClosedEmbedding (fun h : H => h.val * y) :=
  (Homeomorph.mulRight y).isClosedEmbedding.comp hH.isClosedEmbedding_subtypeVal

/-- The weighted slice `h ↦ f(h y) δ_G(h)⁻¹`, a test function on `H`. -/
def slice (f : SchwartzBruhat G) (y : G) : SchwartzBruhat H :=
  ⟨fun h => f (h.val * y) * modularWeight h.val,
    (f.locallyConstant.comp_continuous (continuous_subtype_val.mul continuous_const)).comp₂
      (modularWeight_isLocallyConstant.comp_continuous continuous_subtype_val) (· * ·),
    HasCompactSupport.intro' ((isClosedEmbedding_slice hH y).isCompact_preimage
        (Hecke.TestFunction.isCompact_support f))
      ((Hecke.TestFunction.isClopen_support f).isClosed.preimage
        (continuous_subtype_val.mul continuous_const))
      (fun h hh => by
        have hz : f (h.val * y) = 0 := Function.notMem_support.mp hh
        change f (h.val * y) * modularWeight h.val = 0
        rw [hz, zero_mul])⟩

theorem slice_apply (f : SchwartzBruhat G) (y : G) (h : H) :
    slice hH f y h = f (h.val * y) * modularWeight h.val := rfl

variable [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
variable (μH : Measure H) [μH.IsHaarMeasure]

/-- The averaging integral `y ↦ ∫_H f(h y) δ_G(h)⁻¹ dh`. -/
def average (f : SchwartzBruhat G) (y : G) : ℂ :=
  Distribution.ofMeasure μH (slice hH f y)

theorem average_eq (f : SchwartzBruhat G) (y : G) :
    average hH μH f y = ∫ h : H, f (h.val * y) * modularWeight h.val ∂μH := rfl

theorem integrable_slice (f : SchwartzBruhat G) (y : G) :
    Integrable (fun h : H => f (h.val * y) * modularWeight h.val) μH :=
  Distribution.test_integrable μH (slice hH f y)

theorem average_rightTests (g : G) (f : SchwartzBruhat G) (y : G) :
    average hH μH (GroupAction.rightTests g f) y = average hH μH f (y * g) := by
  unfold average
  congr 1
  apply Hecke.TestFunction.ext
  intro h
  simp only [slice_apply, GroupAction.rightTests_apply, mul_assoc]

theorem average_isLocallyConstant (f : SchwartzBruhat G) :
    IsLocallyConstant (average hH μH f) := by
  obtain ⟨K, -, hK⟩ := exists_right_stabilizer_test f
  apply isLocallyConstant_of_stabilizer K
  intro k x
  unfold average
  congr 1
  apply Hecke.TestFunction.ext
  intro h
  simp only [slice_apply, ← mul_assoc, hK]

theorem relativeModular_apply (h : H) :
    relativeModular H hH h =
      Distribution.renardModular h.val / Distribution.renardModular (G := H) h := rfl

theorem average_mul_left (f : SchwartzBruhat G) (h₀ : H) (y : G) :
    average hH μH f (h₀.val * y) =
      ((relativeModular H hH h₀ : ℝ) : ℂ) * average hH μH f y := by
  have htr := (Distribution.RenardModular.translation H μH).2 (slice hH f y) h₀⁻¹ 1
  have hpt : ∀ x : H, f (x.val * (h₀.val * y)) * modularWeight x.val =
      ((Distribution.renardModular h₀.val : ℝ) : ℂ) * slice hH f y (1 * x * h₀⁻¹⁻¹) := by
    intro x
    simp only [slice_apply, one_mul, inv_inv, Subgroup.coe_mul, modularWeight_mul]
    rw [mul_assoc x.val h₀.val y]
    linear_combination -(f (x.val * (h₀.val * y)) * modularWeight x.val) *
      modularWeight_mul_modular h₀.val
  calc average hH μH f (h₀.val * y)
      = ∫ x : H, ((Distribution.renardModular h₀.val : ℝ) : ℂ) *
          slice hH f y (1 * x * h₀⁻¹⁻¹) ∂μH := by
        rw [average_eq]
        exact congrArg (fun F : H → ℂ => ∫ x, F x ∂μH) (funext hpt)
    _ = ((Distribution.renardModular h₀.val : ℝ) : ℂ) *
          (((Distribution.renardModular (G := H) h₀⁻¹ : ℝ) : ℂ) * average hH μH f y) := by
        rw [integral_const_mul, htr]
        rfl
    _ = ((relativeModular H hH h₀ : ℝ) : ℂ) * average hH μH f y := by
        rw [relativeModular_apply, map_inv]
        push_cast
        ring

theorem exists_ne_zero_of_average_ne_zero {f : SchwartzBruhat G} {y : G}
    (hy : average hH μH f y ≠ 0) : ∃ h : H, f (h.val * y) ≠ 0 := by
  by_contra hall
  simp only [not_exists, not_not] at hall
  apply hy
  have hs : slice hH f y = 0 := Hecke.TestFunction.ext fun h => by
    change f (h.val * y) * modularWeight h.val = 0
    rw [hall h, zero_mul]
  rw [average, hs, map_zero]

/-- The average of a test function, as a vector of the twisted space. -/
def averageVec (f : SchwartzBruhat G) : renardSpace H hH :=
  ⟨⟨average hH μH f, average_isLocallyConstant hH μH f⟩,
    fun h y => average_mul_left hH μH f h y,
    ⟨Function.support f, Hecke.TestFunction.isCompact_support f, by
      intro y hy
      obtain ⟨h, hh⟩ := exists_ne_zero_of_average_ne_zero hH μH hy
      exact ⟨(h.val)⁻¹, H.inv_mem h.property, h.val * y, hh, by group⟩⟩⟩

theorem averageVec_apply (f : SchwartzBruhat G) (y : G) :
    (averageVec hH μH f).val y = average hH μH f y := rfl

/-- The averaging map of Renard II.3.9. -/
def averaging : SchwartzBruhat G →ₗ[ℂ] renardSpace H hH where
  toFun := averageVec hH μH
  map_add' f g := by
    apply Subtype.ext
    apply LocallyConstant.ext
    intro y
    show average hH μH (f + g) y = average hH μH f y + average hH μH g y
    unfold average
    rw [← map_add]
    congr 1
    exact Hecke.TestFunction.ext fun h => add_mul _ _ _
  map_smul' c f := by
    apply Subtype.ext
    apply LocallyConstant.ext
    intro y
    show average hH μH (c • f) y = c * average hH μH f y
    unfold average
    rw [← smul_eq_mul, ← map_smul]
    congr 1
    exact Hecke.TestFunction.ext fun h => mul_assoc _ _ _

theorem averaging_apply (f : SchwartzBruhat G) (y : G) :
    (averaging hH μH f).val y = ∫ h : H, f (h.val * y) * modularWeight h.val ∂μH := rfl

theorem averaging_rightTests (g : G) (f : SchwartzBruhat G) :
    averaging hH μH (GroupAction.rightTests g f) =
      rightAction H (relativeModular H hH) g (averaging hH μH f) := by
  apply Subtype.ext
  apply LocallyConstant.ext
  intro y
  exact average_rightTests hH μH g f y

end Averaging


/-! ## Evaluation maps -/

section Evaluation

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Evaluation of test functions at a point, as a linear form. -/
def evalTest (x : G) : SchwartzBruhat G →ₗ[ℂ] ℂ where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evalTest_apply (x : G) (f : SchwartzBruhat G) : evalTest x f = f x := rfl

variable [LocallyCompactSpace G] (H : Subgroup G) (χ : H →* ℝ≥0)

/-- Evaluation of twisted functions at a point, as a linear form. -/
def evalSpace (x : G) : space H χ →ₗ[ℂ] ℂ where
  toFun F := F.val x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evalSpace_apply (x : G) (F : space H χ) : evalSpace H χ x F = F.val x := rfl

end Evaluation

/-! ## Cosets of a compact open subgroup -/

section Cosets

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (K : OpenSubgroup G)

/-- The left coset `a K`, written as in `rightInvariantExpansion`. -/
def coset (a : G) : Set G := {y | ∃ k : K, y = a * (k : G)}

theorem mem_coset_iff (a y : G) : y ∈ coset K a ↔ a⁻¹ * y ∈ K := by
  constructor
  · rintro ⟨k, rfl⟩
    simp
  · intro h
    exact ⟨⟨a⁻¹ * y, h⟩, by simp⟩

theorem mem_coset_self (a : G) : a ∈ coset K a := ⟨1, by simp⟩

theorem isClopen_coset (a : G) : IsClopen (coset K a) := by
  have he : coset K a = (fun y => a⁻¹ * y) ⁻¹' (K : Set G) := by
    ext y
    exact mem_coset_iff K a y
  rw [he]
  exact K.isClopen.preimage (continuous_const.mul continuous_id)

theorem isCompact_coset (hKc : IsCompact (K : Set G)) (a : G) : IsCompact (coset K a) := by
  have he : coset K a = (fun y => a * y) '' (K : Set G) := by
    ext y
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, k.property, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  rw [he]
  exact hKc.image (continuous_const.mul continuous_id)

theorem mem_coset_mul_left (h a y : G) : y ∈ coset K (h * a) ↔ h⁻¹ * y ∈ coset K a := by
  rw [mem_coset_iff, mem_coset_iff, mul_inv_rev, mul_assoc]

theorem mem_coset_mul_right (a y : G) (k : K) : y ∈ coset K (a * k) ↔ y ∈ coset K a := by
  rw [mem_coset_iff, mem_coset_iff, mul_inv_rev, mul_assoc]
  constructor
  · intro hy
    simpa using K.mul_mem k.property hy
  · intro hy
    exact K.mul_mem (K.inv_mem k.property) hy

theorem mem_coset_mul_stab (a y : G) (k : K) : y * k ∈ coset K a ↔ y ∈ coset K a := by
  rw [mem_coset_iff, mem_coset_iff, ← mul_assoc]
  constructor
  · intro hy
    simpa using K.mul_mem hy (K.inv_mem k.property)
  · intro hy
    exact K.mul_mem hy k.property

variable (hKc : IsCompact (K : Set G))

/-- The characteristic test function of the coset `a K`. -/
def cosetTest (a : G) : SchwartzBruhat G :=
  Hecke.TestFunction.characteristic (isClopen_coset K a) (isCompact_coset K hKc a)

theorem cosetTest_apply (a y : G) :
    cosetTest K hKc a y = (coset K a).indicator (fun _ => (1 : ℂ)) y := rfl

theorem cosetTest_apply_of_mem {a y : G} (h : y ∈ coset K a) : cosetTest K hKc a y = 1 := by
  rw [cosetTest_apply, Set.indicator_of_mem h]

theorem cosetTest_apply_of_notMem {a y : G} (h : y ∉ coset K a) :
    cosetTest K hKc a y = 0 := by
  rw [cosetTest_apply, Set.indicator_of_notMem h]

theorem cosetTest_nonneg (a y : G) : 0 ≤ cosetTest K hKc a y := by
  by_cases h : y ∈ coset K a
  · rw [cosetTest_apply_of_mem K hKc h]
    exact zero_le_one
  · rw [cosetTest_apply_of_notMem K hKc h]

theorem cosetTest_mul_stab (a : G) (k : K) (y : G) :
    cosetTest K hKc a (y * k) = cosetTest K hKc a y := by
  simp only [cosetTest_apply, Set.indicator]
  classical
  exact if_congr (mem_coset_mul_stab K a y k) rfl rfl

theorem cosetTest_mul_left (h a : G) :
    cosetTest K hKc (h * a) = GroupAction.leftTests h (cosetTest K hKc a) := by
  apply Hecke.TestFunction.ext
  intro y
  rw [GroupAction.leftTests_apply, cosetTest_apply, cosetTest_apply]
  simp only [Set.indicator]
  classical
  exact if_congr (mem_coset_mul_left K h a y) rfl rfl

theorem cosetTest_mul_right (a : G) (k : K) :
    cosetTest K hKc (a * k) = cosetTest K hKc a := by
  apply Hecke.TestFunction.ext
  intro y
  simp only [cosetTest_apply, Set.indicator]
  classical
  exact if_congr (mem_coset_mul_right K a y k) rfl rfl

/-- The double coset `H a K`. -/
def dcoset (H : Subgroup G) (a : G) : Set G := {x | ∃ (h : H) (k : K), x = h.val * a * k}

theorem mem_dcoset_self (H : Subgroup G) (a : G) : a ∈ dcoset K H a := ⟨1, 1, by simp⟩

theorem dcoset_eq_of_mem {H : Subgroup G} {a y : G} (hy : y ∈ dcoset K H a) :
    dcoset K H y = dcoset K H a := by
  obtain ⟨h₀, k₀, rfl⟩ := hy
  ext x
  constructor
  · rintro ⟨h, k, rfl⟩
    refine ⟨h * h₀, k₀ * k, ?_⟩
    simp only [MulMemClass.coe_mul]
    group
  · rintro ⟨h, k, rfl⟩
    refine ⟨h * h₀⁻¹, k₀⁻¹ * k, ?_⟩
    simp only [MulMemClass.coe_mul, InvMemClass.coe_inv]
    group

end Cosets

/-- An abstract cancellation lemma: if the sums `∑ⱼ cⱼ P i j` vanish, where `P i j`
vanishes across classes, is nonzero on the diagonal, and within a class is
proportional to `t` in the displayed way, then `∑ⱼ cⱼ tⱼ = 0`. -/
theorem sum_eq_zero_of_classes {ι α : Type*} [DecidableEq α] (s : Finset ι) (D : ι → α)
    (c t : ι → ℂ) (P : ι → ι → ℂ)
    (hzero : ∀ i ∈ s, ∀ j ∈ s, D i ≠ D j → P i j = 0)
    (hcross : ∀ i ∈ s, ∀ j ∈ s, D i = D j → t j * P i i = t i * P i j)
    (hdiag : ∀ i ∈ s, P i i ≠ 0)
    (hsum : ∀ i ∈ s, ∑ j ∈ s, c j * P i j = 0) :
    ∑ j ∈ s, c j * t j = 0 := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := D) (t := s.image D)
    (fun i hi => Finset.mem_image_of_mem D hi)]
  apply Finset.sum_eq_zero
  intro a ha
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  have hfil : ∑ j ∈ s with D j = D i, c j * P i j = ∑ j ∈ s, c j * P i j := by
    apply Finset.sum_filter_of_ne
    intro j hj hne
    by_contra hD
    exact hne (by rw [hzero i hi j hj (Ne.symm hD), mul_zero])
  have hmul : P i i * ∑ j ∈ s with D j = D i, c j * t j =
      t i * ∑ j ∈ s with D j = D i, c j * P i j := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hD := Finset.mem_filter.mp hj
    have hc := hcross i hi j hD.1 hD.2.symm
    linear_combination c j * hc
  rw [hfil, hsum i hi, mul_zero] at hmul
  exact (mul_eq_zero.mp hmul).resolve_left (hdiag i hi)

/-! ## Averages of coset tests, the kernel and surjectivity -/

section Kernel

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
variable {H : Subgroup G} (hH : IsClosed (H : Set G))
include hH
variable [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
variable (μH : Measure H) [μH.IsHaarMeasure]

theorem average_leftTests (h : H) (φ : SchwartzBruhat G) (y : G) :
    average hH μH (GroupAction.leftTests h.val φ) y =
      modularWeight h.val * average hH μH φ y := by
  have hpt : ∀ x : H, GroupAction.leftTests h.val φ (x.val * y) * modularWeight x.val =
      modularWeight h.val * slice hH φ y (h⁻¹ * x) := by
    intro x
    have hw : modularWeight x.val = modularWeight h.val * modularWeight (h⁻¹ * x).val := by
      rw [← modularWeight_mul]
      congr 1
      simp
    rw [hw, GroupAction.leftTests_apply, slice_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
    ring
  calc average hH μH (GroupAction.leftTests h.val φ) y
      = ∫ x : H, modularWeight h.val * slice hH φ y (h⁻¹ * x) ∂μH := by
        rw [average_eq]
        exact congrArg (fun F : H → ℂ => ∫ x, F x ∂μH) (funext hpt)
    _ = modularWeight h.val * average hH μH φ y := by
        rw [integral_const_mul]
        congr 1
        exact integral_mul_left_eq_self (μ := μH) (fun x => slice hH φ y x) h⁻¹

theorem average_nonneg {f : SchwartzBruhat G} (hf : ∀ x, 0 ≤ f x) (y : G) :
    0 ≤ average hH μH f y := by
  by_cases hs : slice hH f y = 0
  · rw [average, hs, map_zero]
  · have hpos := Distribution.RenardHaar.ofMeasure_positive μH (slice hH f y) hs
      (fun h => (complex_nonneg_iff _).mp (mul_nonneg (hf _) (modularWeight_nonneg _)))
    exact Complex.nonneg_iff.mpr ⟨hpos.2.le, hpos.1.symm⟩

theorem average_pos {f : SchwartzBruhat G} (hf : ∀ x, 0 ≤ f x) {y : G} (hy : f y ≠ 0) :
    0 < average hH μH f y := by
  have hs : slice hH f y ≠ 0 := by
    intro hz
    have h1 : slice hH f y 1 = f y := by
      rw [slice_apply, OneMemClass.coe_one, one_mul, modularWeight_one, mul_one]
    rw [hz] at h1
    exact hy (h1.symm.trans rfl)
  have hpos := Distribution.RenardHaar.ofMeasure_positive μH (slice hH f y) hs
    (fun h => (complex_nonneg_iff _).mp (mul_nonneg (hf _) (modularWeight_nonneg _)))
  exact Complex.pos_iff.mpr ⟨hpos.2, hpos.1.symm⟩

theorem average_mul_stab {φ : SchwartzBruhat G} {K : OpenSubgroup G}
    (hφ : ∀ (k : K) (x : G), φ (x * k) = φ x) (k : K) (y : G) :
    average hH μH φ (y * k) = average hH μH φ y := by
  rw [← average_rightTests]
  congr 1
  apply Hecke.TestFunction.ext
  intro x
  rw [GroupAction.rightTests_apply, hφ]

theorem averaging_ne_zero {f : SchwartzBruhat G} (hf : ∀ x, 0 ≤ f x) (hf0 : f ≠ 0) :
    averaging hH μH f ≠ 0 := by
  obtain ⟨y, hy⟩ : ∃ y, f y ≠ 0 := by
    by_contra hall
    simp only [ne_eq, not_exists, not_not] at hall
    exact hf0 (Hecke.TestFunction.ext fun x => hall x)
  intro hz
  have hval : (averaging hH μH f).val y = 0 := by rw [hz]; rfl
  exact (average_pos hH μH hf hy).ne' hval

theorem averaging_nonneg {f : SchwartzBruhat G} (hf : ∀ x, 0 ≤ f x) (y : G) :
    0 ≤ (averaging hH μH f).val y :=
  average_nonneg hH μH hf y

variable (K : OpenSubgroup G) (hKc : IsCompact (K : Set G))

theorem average_cosetTest_eq_zero {a y : G} (hy : y ∉ dcoset K H a) :
    average hH μH (cosetTest K hKc a) y = 0 := by
  by_contra hne
  obtain ⟨h, hh⟩ := exists_ne_zero_of_average_ne_zero hH μH hne
  apply hy
  have hmem : h.val * y ∈ coset K a := by
    by_contra hn
    exact hh (cosetTest_apply_of_notMem K hKc hn)
  obtain ⟨k, hk⟩ := hmem
  exact ⟨h⁻¹, k, by rw [Subgroup.coe_inv, mul_assoc, ← hk, inv_mul_cancel_left]⟩

theorem average_cosetTest_self_pos (a : G) : 0 < average hH μH (cosetTest K hKc a) a :=
  average_pos hH μH (cosetTest_nonneg K hKc a)
    (by rw [cosetTest_apply_of_mem K hKc (mem_coset_self K a)]; exact one_ne_zero)

end Kernel

/-! ## The inverted Haar functional -/

section Inverse

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] (μG : Measure G) [μG.IsHaarMeasure]

theorem ofMeasure_inv_apply (f : SchwartzBruhat G) :
    Distribution.ofMeasure μG.inv f = ∫ x, f x⁻¹ ∂μG := by
  rw [Distribution.ofMeasure_apply, Measure.inv,
    integral_map measurable_inv.aemeasurable f.continuous.aestronglyMeasurable]

theorem ofMeasure_inv_eq :
    Distribution.ofMeasure μG.inv =
      GroupAction.inversionDistributions (Distribution.ofMeasure μG) := by
  apply LinearMap.ext
  intro f
  rw [ofMeasure_inv_apply, GroupAction.inversionDistributions_apply,
    Distribution.ofMeasure_apply]
  rfl

theorem inverse_positive : Distribution.IsPositive (Distribution.ofMeasure μG.inv) := by
  rw [ofMeasure_inv_eq]
  exact Distribution.RenardHaar.isPositive_inversion
    (Distribution.RenardHaar.ofMeasure_positive μG)

theorem inverse_leftTests (h : G) (φ : SchwartzBruhat G) :
    Distribution.ofMeasure μG.inv (GroupAction.leftTests h φ) =
      modularWeight h * Distribution.ofMeasure μG.inv φ := by
  rw [ofMeasure_inv_apply, ofMeasure_inv_apply, modularWeight_eq_inv]
  have htr := (Distribution.RenardModular.translation G μG).2
    (GroupAction.inversionTests φ) h⁻¹ 1
  have hpt : ∀ x : G, GroupAction.leftTests h φ x⁻¹ =
      GroupAction.inversionTests φ (1 * x * h⁻¹⁻¹) := by
    intro x
    rw [GroupAction.leftTests_apply, GroupAction.inversionTests_apply, one_mul, inv_inv,
      mul_inv_rev]
  calc ∫ x, GroupAction.leftTests h φ x⁻¹ ∂μG
      = ∫ x, GroupAction.inversionTests φ (1 * x * h⁻¹⁻¹) ∂μG :=
        congrArg (fun F : G → ℂ => ∫ x, F x ∂μG) (funext hpt)
    _ = _ := htr

theorem inverse_rightTests (g : G) (f : SchwartzBruhat G) :
    Distribution.ofMeasure μG.inv (GroupAction.rightTests g f) =
      Distribution.ofMeasure μG.inv f := by
  rw [ofMeasure_inv_apply, ofMeasure_inv_apply]
  have hpt : ∀ x : G, GroupAction.rightTests g f x⁻¹ = f (g⁻¹ * x)⁻¹ := by
    intro x
    rw [GroupAction.rightTests_apply, mul_inv_rev, inv_inv]
  calc ∫ x, GroupAction.rightTests g f x⁻¹ ∂μG = ∫ x, f (g⁻¹ * x)⁻¹ ∂μG :=
        congrArg (fun F : G → ℂ => ∫ x, F x ∂μG) (funext hpt)
    _ = ∫ x, f x⁻¹ ∂μG := integral_mul_left_eq_self (fun x => f x⁻¹) g⁻¹

end Inverse

/-! ## Kernel, surjectivity and the descended functional -/

section Functional

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] (μG : Measure G) [μG.IsHaarMeasure]
variable {H : Subgroup G} (hH : IsClosed (H : Set G))
include hH
variable [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
variable (μH : Measure H) [μH.IsHaarMeasure]

theorem expansion_eq {f : SchwartzBruhat G} {K : OpenSubgroup G} (hKc : IsCompact (K : Set G))
    {n : ℕ} {g : Fin n → G} {c : Fin n → ℂ}
    (hexp : ∀ x : G, f x = ∑ i, c i *
      ({y | ∃ k : K, y = g i * (k : G)} : Set G).indicator (fun _ => 1) x) :
    f = ∑ i, c i • cosetTest K hKc (g i) := by
  apply Hecke.TestFunction.ext
  intro x
  change f x = evalTest x (∑ i, c i • cosetTest K hKc (g i))
  rw [map_sum]
  simp only [map_smul, evalTest_apply, smul_eq_mul, cosetTest_apply]
  exact hexp x

omit [MeasurableSpace G] [BorelSpace G] in
theorem averaging_sum_apply (K : OpenSubgroup G) (hKc : IsCompact (K : Set G))
    {n : ℕ} (g : Fin n → G) (c : Fin n → ℂ) (y : G) :
    (averaging hH μH (∑ j, c j • cosetTest K hKc (g j))).val y =
      ∑ j, c j * average hH μH (cosetTest K hKc (g j)) y := by
  change evalSpace H (relativeModular H hH) y
    (averaging hH μH (∑ j, c j • cosetTest K hKc (g j))) = _
  rw [map_sum, map_sum]
  simp only [map_smul, smul_eq_mul]
  rfl

/-- The kernel of the averaging map is killed by the inverted Haar functional. -/
theorem inverse_eq_zero_of_averaging_eq_zero {f : SchwartzBruhat G}
    (hf : averaging hH μH f = 0) : Distribution.ofMeasure μG.inv f = 0 := by
  classical
  obtain ⟨K, hKc, hK⟩ := exists_right_stabilizer_test f
  obtain ⟨n, g, c, -, -, -, hexp⟩ :=
    Hecke.RenardTestDecomposition.rightInvariantExpansion G K hKc f
      (fun k => Hecke.TestFunction.ext fun x => by
        rw [Hecke.TestFunction.rightTranslate_apply, hK])
  have hfe := expansion_eq hH hKc hexp
  rw [hfe, map_sum]
  simp only [map_smul, smul_eq_mul]
  apply sum_eq_zero_of_classes Finset.univ (fun i => dcoset K H (g i)) c
    (fun j => Distribution.ofMeasure μG.inv (cosetTest K hKc (g j)))
    (fun i j => average hH μH (cosetTest K hKc (g j)) (g i))
  · intro i _ j _ hne
    apply average_cosetTest_eq_zero hH μH K hKc
    intro hmem
    exact hne (dcoset_eq_of_mem K hmem)
  · intro i _ j _ hD
    have hD' : dcoset K H (g i) = dcoset K H (g j) := hD
    have hmem : g j ∈ dcoset K H (g i) := by
      rw [hD']
      exact mem_dcoset_self K H (g j)
    obtain ⟨h, k, hjk⟩ := hmem
    have he : cosetTest K hKc (g j) = GroupAction.leftTests h.val (cosetTest K hKc (g i)) := by
      rw [hjk, cosetTest_mul_right, cosetTest_mul_left]
    rw [he, average_leftTests, inverse_leftTests]
    ring
  · intro i _
    exact (average_cosetTest_self_pos hH μH K hKc (g i)).ne'
  · intro i _
    have h1 := averaging_sum_apply hH μH K hKc g c (g i)
    rw [← hfe, hf] at h1
    exact h1.symm

omit [MeasurableSpace G] [BorelSpace G] in
/-- One induction step of surjectivity: covering the support by finitely many
double cosets `H x K`. -/
theorem exists_averaging_eq_of_cover (K : OpenSubgroup G) (hKc : IsCompact (K : Set G))
    (S : Finset G) : ∀ F : renardSpace H hH, (∀ (k : K) (y : G), F.val (y * k) = F.val y) →
      (∀ y, F.val y ≠ 0 → ∃ x ∈ S, y ∈ dcoset K H x) →
      ∃ f : SchwartzBruhat G, averaging hH μH f = F ∧
        ((∀ y, 0 ≤ F.val y) → ∀ y, 0 ≤ f y) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro F _ hcov
    refine ⟨0, ?_, fun _ _ => le_refl (0 : ℂ)⟩
    rw [map_zero]
    apply Subtype.ext
    apply LocallyConstant.ext
    intro y
    by_contra hne
    have hy : F.val y ≠ 0 := fun h => hne (by rw [h]; rfl)
    obtain ⟨x, hx, -⟩ := hcov y hy
    exact Finset.notMem_empty x hx
  | insert x S hxS ih =>
    intro F hFK hcov
    obtain ⟨c, hc, hcnn⟩ : ∃ c : ℂ, c * average hH μH (cosetTest K hKc x) x = F.val x ∧
        ((∀ y, 0 ≤ F.val y) → 0 ≤ c) := by
      have hpos := average_cosetTest_self_pos hH μH K hKc x
      generalize average hH μH (cosetTest K hKc x) x = a at hpos ⊢
      obtain ⟨hre, him⟩ := Complex.pos_iff.mp hpos
      have ha : a = (a.re : ℂ) :=
        Complex.ext (Complex.ofReal_re _).symm (by rw [Complex.ofReal_im]; exact him.symm)
      refine ⟨F.val x * ((a.re⁻¹ : ℝ) : ℂ), ?_, fun hnn =>
        mul_nonneg (hnn x) (Complex.zero_le_real.mpr (inv_nonneg.mpr hre.le))⟩
      calc F.val x * ((a.re⁻¹ : ℝ) : ℂ) * a = F.val x * ((a.re⁻¹ : ℝ) : ℂ) * (a.re : ℂ) := by
            rw [← ha]
        _ = F.val x := by
            rw [mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hre.ne', Complex.ofReal_one,
              mul_one]
    have heK : ∀ (k : K) (y : G),
        average hH μH (cosetTest K hKc x) (y * k) = average hH μH (cosetTest K hKc x) y :=
      fun k y => average_mul_stab hH μH (fun k y => cosetTest_mul_stab K hKc x k y) k y
    let F' : renardSpace H hH := F - c • averaging hH μH (cosetTest K hKc x)
    have hF'val : ∀ y, F'.val y = F.val y - c * average hH μH (cosetTest K hKc x) y :=
      fun y => rfl
    have hzero : ∀ y ∈ dcoset K H x, F'.val y = 0 := by
      rintro y ⟨h, k, rfl⟩
      rw [hF'val, hFK, heK, F.property.1 h x, average_mul_left hH μH _ h x, ← hc]
      ring
    have hoff : ∀ y ∉ dcoset K H x, F'.val y = F.val y := by
      intro y hy
      rw [hF'val, average_cosetTest_eq_zero hH μH K hKc hy, mul_zero, sub_zero]
    have hF'K : ∀ (k : K) (y : G), F'.val (y * k) = F'.val y := by
      intro k y
      rw [hF'val, hF'val, hFK, heK]
    have hF'cov : ∀ y, F'.val y ≠ 0 → ∃ x' ∈ S, y ∈ dcoset K H x' := by
      intro y hy
      have hyx : y ∉ dcoset K H x := fun hm => hy (hzero y hm)
      obtain ⟨x', hx', hyx'⟩ := hcov y (by rwa [← hoff y hyx])
      rcases Finset.mem_insert.mp hx' with rfl | hS
      · exact absurd hyx' hyx
      · exact ⟨x', hS, hyx'⟩
    obtain ⟨f', hf', hf'nn⟩ := ih F' hF'K hF'cov
    refine ⟨f' + c • cosetTest K hKc x, ?_, ?_⟩
    · rw [map_add, map_smul, hf']
      exact sub_add_cancel F _
    · intro hnn y
      have hF'nn : ∀ y, 0 ≤ F'.val y := by
        intro y
        by_cases hy : y ∈ dcoset K H x
        · simp only [hzero y hy, le_refl]
        · rw [hoff y hy]
          exact hnn y
      show 0 ≤ f' y + c * cosetTest K hKc x y
      exact add_nonneg (hf'nn hF'nn y) (mul_nonneg (hcnn hnn) (cosetTest_nonneg K hKc x y))

omit [MeasurableSpace G] [BorelSpace G] in
/-- Surjectivity of the averaging map, with nonnegative preimages of nonnegative
functions. -/
theorem exists_averaging_eq (F : renardSpace H hH) :
    ∃ f : SchwartzBruhat G, averaging hH μH f = F ∧
      ((∀ y, 0 ≤ F.val y) → ∀ y, 0 ≤ f y) := by
  obtain ⟨K, hKc, hK⟩ := exists_uniform_stabilizer H (relativeModular H hH) F
  obtain ⟨C, hC, hsupp⟩ := F.property.2
  obtain ⟨S, -, hcover⟩ := hC.elim_nhds_subcover (fun x => coset K x)
    (fun x _ => (isClopen_coset K x).isOpen.mem_nhds (mem_coset_self K x))
  apply exists_averaging_eq_of_cover hH μH K hKc S F hK
  intro y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hsupp hy
  obtain ⟨x, hxS, hbx⟩ := Set.mem_iUnion₂.mp (hcover hb)
  obtain ⟨k, hk⟩ := hbx
  exact ⟨x, hxS, ⟨a, ha⟩, k, by rw [hk]; exact (mul_assoc _ _ _).symm⟩

omit [MeasurableSpace G] [BorelSpace G] in
theorem averaging_surjective : Function.Surjective (averaging hH μH) := fun F =>
  (exists_averaging_eq hH μH F).imp fun _ h => h.1

/-- The descended functional. -/
theorem exists_functional : ∃ ν : Module.Dual ℂ (renardSpace H hH),
    ν.comp (averaging hH μH) = Distribution.ofMeasure μG.inv ∧
    ∀ (g : G) (F : renardSpace H hH),
      ν (rightAction H (relativeModular H hH) g F) = ν F := by
  obtain ⟨s, hs⟩ := (averaging hH μH).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (averaging_surjective hH μH))
  have hcomp : ((Distribution.ofMeasure μG.inv).comp s).comp (averaging hH μH) =
      Distribution.ofMeasure μG.inv := by
    apply LinearMap.ext
    intro f
    have hps : averaging hH μH (s (averaging hH μH f)) = averaging hH μH f :=
      LinearMap.congr_fun hs (averaging hH μH f)
    have hk : averaging hH μH (s (averaging hH μH f) - f) = 0 := by
      rw [map_sub, hps, sub_self]
    have h0 := inverse_eq_zero_of_averaging_eq_zero μG hH μH hk
    rw [map_sub, sub_eq_zero] at h0
    exact h0
  refine ⟨(Distribution.ofMeasure μG.inv).comp s, hcomp, ?_⟩
  intro g F
  obtain ⟨f, rfl⟩ := averaging_surjective hH μH F
  rw [← averaging_rightTests]
  have h1 := LinearMap.congr_fun hcomp (GroupAction.rightTests g f)
  have h2 := LinearMap.congr_fun hcomp f
  simp only [LinearMap.comp_apply] at h1 h2 ⊢
  rw [h1, h2, inverse_rightTests]

end Functional

/-! ## The two statements -/

theorem averagingStatement : AveragingStatement.{uG} := by
  intro G _ _ _ _ _ _ _ _ μG _ H hH
  let _ : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let _ : MeasurableSpace H := borel H
  have _ : BorelSpace H := ⟨rfl⟩
  intro μH _
  obtain ⟨ν, hν, hνinv⟩ := exists_functional μG hH μH
  refine ⟨averaging hH μH, fun f g => ?_, fun f g => ?_, averaging_surjective hH μH,
    averaging_rightTests hH μH, ν, hν, hνinv⟩
  · simpa only [modularWeight_eq_inv_cast] using integrable_slice hH μH f g
  · rw [averaging_apply]
    simp only [modularWeight_eq_inv_cast]

theorem invariantFunctional : InvariantFunctionalStatement.{uG} := by
  intro G _ _ _ _ _ _ H hH
  dsimp only
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  let _ : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let _ : MeasurableSpace H := borel H
  have _ : BorelSpace H := ⟨rfl⟩
  obtain ⟨μG, hμG⟩ : ∃ μ : Measure G, μ.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  obtain ⟨μH, hμH⟩ : ∃ μ : Measure H, μ.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  obtain ⟨ν, hνp, hνinv⟩ := exists_functional μG hH μH
  have hTpos := inverse_positive μG
  have hsurj := averaging_surjective hH μH
  have hcomp_inj : ∀ S S' : Module.Dual ℂ (renardSpace H hH),
      S.comp (averaging hH μH) = S'.comp (averaging hH μH) → S = S' :=
    fun S S' h => (LinearMap.cancel_right hsurj).mp h
  have hν0 : ν ≠ 0 := by
    intro h0
    apply Distribution.RenardHaar.ne_zero_of_isPositive hTpos
    rw [← hνp, h0, LinearMap.zero_comp]
  have hpos : ∀ F : renardSpace H hH, F ≠ 0 →
      (∀ x, (F.val x).im = 0 ∧ 0 ≤ (F.val x).re) → (ν F).im = 0 ∧ 0 < (ν F).re := by
    intro F hF hFnn
    obtain ⟨f, hf, hfnn⟩ := exists_averaging_eq hH μH F
    have hfnn' := hfnn (fun x => (complex_nonneg_iff _).mpr (hFnn x))
    have hf0 : f ≠ 0 := by
      rintro rfl
      exact hF (by rw [← hf, map_zero])
    have hνf : ν F = Distribution.ofMeasure μG.inv f := by
      rw [← hf, ← LinearMap.comp_apply, hνp]
    rw [hνf]
    exact hTpos f hf0 (fun x => (complex_nonneg_iff _).mp (hfnn' x))
  have huniq : ∀ S : Module.Dual ℂ (renardSpace H hH),
      (∀ (g : G) (F : renardSpace H hH),
        S (rightAction H (relativeModular H hH) g F) = S F) →
      ∃ c : ℂ, S.comp (averaging hH μH) = c • Distribution.ofMeasure μG.inv ∧ S = c • ν := by
    intro S hS
    have hD : Distribution.IsRightInvariant (S.comp (averaging hH μH)) := by
      intro g
      apply LinearMap.ext
      intro f
      rw [GroupAction.rightDistributions_apply, LinearMap.comp_apply, LinearMap.comp_apply,
        averaging_rightTests, hS]
    obtain ⟨c, hc, -⟩ := (Distribution.RenardHaar.measureHaarBridge G μG).2.2 _
      (Distribution.RenardHaar.isLeftInvariant_inversion hD)
    have hc' : S.comp (averaging hH μH) = c • Distribution.ofMeasure μG.inv := by
      have h := congrArg GroupAction.inversionDistributions hc
      rw [GroupAction.inversionDistributions_inversionDistributions, map_smul,
        ← ofMeasure_inv_eq] at h
      exact h
    refine ⟨c, hc', hcomp_inj _ _ ?_⟩
    rw [hc', LinearMap.smul_comp, hνp]
  refine ⟨ν, hpos, hνinv, ?_, ?_⟩
  · intro S hS
    obtain ⟨c, -, hc⟩ := huniq S hS
    refine ⟨c, hc, fun d hd => ?_⟩
    exact smul_left_injective ℂ hν0 (hd.symm.trans hc)
  · intro S hSpos hS
    obtain ⟨c, hcT, -⟩ := huniq S hS
    have hDpos : Distribution.IsPositive (S.comp (averaging hH μH)) := by
      intro f hf hfnn
      have hnn : ∀ x, 0 ≤ f x := fun x => (complex_nonneg_iff _).mpr (hfnn x)
      exact hSpos (averaging hH μH f) (averaging_ne_zero hH μH hnn hf)
        (fun x => (complex_nonneg_iff _).mp (averaging_nonneg hH μH hnn x))
    obtain ⟨r, ⟨hr, hrT⟩, hru⟩ :=
      Distribution.RenardHaar.positive_real_multiple hTpos hDpos ⟨c, hcT⟩
    refine ⟨r, ⟨hr, hcomp_inj _ _ (by rw [hrT, LinearMap.smul_comp, hνp])⟩, ?_⟩
    rintro r' ⟨hr', hS'⟩
    exact hru r' ⟨hr', by rw [hS', LinearMap.smul_comp, hνp]⟩

end Langlands.HarmonicAnalysis.HomogeneousFunctions.Renard
