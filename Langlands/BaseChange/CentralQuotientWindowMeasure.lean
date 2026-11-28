import Langlands.Group.GL.LocalFieldTopology
import Langlands.JacquetLanglands.EssentiallySquareIntegrable
import Langlands.Representation.Plancherel.FieldUnitsTopologyProof
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Algebra.Order.Archimedean.Basic

/-! # A Haar measure on `GL_n(F)` modulo its center from a determinant window -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory Set

universe u

section Window

variable {H : Type*} [Group H]

/-- The elements whose degree `w h` lies in the window `[c, c + n)`. -/
def degreeWindow (w : H →* Multiplicative ℤ) (n : ℕ) (c : ℤ) : Set H :=
  {h | c ≤ (w h).toAdd ∧ (w h).toAdd < c + n}

theorem degreeWindow_mul_left (w : H →* Multiplicative ℤ) (n : ℕ) (c : ℤ) (a : H) :
    (fun h => a * h) ⁻¹' degreeWindow w n c = degreeWindow w n (c - (w a).toAdd) := by
  ext h
  simp only [degreeWindow, mem_preimage, mem_ofPred_eq, map_mul, toAdd_mul]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> omega

/-- A degree window of length `n` is a fundamental domain for left multiplication by the
powers of an element of degree `n`. -/
theorem isFundamentalDomain_degreeWindow [MeasurableSpace H] (w : H →* Multiplicative ℤ)
    {n : ℕ} (hn : 0 < n) {s : H} (hs : (w s).toAdd = n) (c : ℤ) (μ : Measure H)
    (hm : MeasurableSet (degreeWindow w n c)) :
    IsFundamentalDomain (Subgroup.zpowers s) (degreeWindow w n c) μ := by
  refine IsFundamentalDomain.mk' hm.nullMeasurableSet fun h => ?_
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  obtain ⟨k, hk, huniq⟩ := existsUnique_add_zsmul_mem_Ico hn' (w h).toAdd c
  have hdeg (j : ℤ) : (w (s ^ j * h)).toAdd = (w h).toAdd + j • (n : ℤ) := by
    rw [map_mul, map_zpow, toAdd_mul, toAdd_zpow, hs, add_comm]
  refine ⟨⟨s ^ k, Subgroup.zpow_mem_zpowers s k⟩, ?_, ?_⟩
  · change c ≤ (w (s ^ k * h)).toAdd ∧ (w (s ^ k * h)).toAdd < c + n
    rw [hdeg]
    exact hk
  · rintro ⟨g, hg⟩ hgh
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    change c ≤ (w (s ^ j * h)).toAdd ∧ (w (s ^ j * h)).toAdd < c + n at hgh
    rw [hdeg] at hgh
    have hj : j = k := huniq j hgh
    subst hj
    rfl

/-- Two windows of length `n` cut the same measure out of every measurable set that is
invariant under left multiplication by the powers of an element `s` of degree `n`, for a
left-invariant measure. -/
theorem measure_inter_degreeWindow_eq [MeasurableSpace H] [MeasurableMul H]
    (w : H →* Multiplicative ℤ) (hw : Measurable fun h => (w h).toAdd)
    {n : ℕ} (hn : 0 < n) {s : H} (hs : (w s).toAdd = n) (μ : Measure H)
    [μ.IsMulLeftInvariant] {A : Set H} (hA : MeasurableSet A)
    (hAs : ∀ (k : ℤ) (h : H), s ^ k * h ∈ A ↔ h ∈ A) (c c' : ℤ) :
    μ (A ∩ degreeWindow w n c) = μ (A ∩ degreeWindow w n c') := by
  have hm (d : ℤ) : MeasurableSet (degreeWindow w n d) :=
    hw (MeasurableSet.of_discrete (s := Ico d (d + n)))
  refine (isFundamentalDomain_degreeWindow w hn hs c μ (hm c)).measure_set_eq
    (isFundamentalDomain_degreeWindow w hn hs c' μ (hm c')) hA ?_
  rintro ⟨g, hg⟩
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  ext h
  exact hAs j h

end Window

section GeneralLinear

open Plancherel

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (n : ℕ)

/-- The valuation-ring units form a compact subset of the field units. -/
theorem isCompact_unitGroup : IsCompact (FML.unitGroup F : Set Fˣ) := by
  let S : Set F := {x | ValuativeRel.valuation F x = 1}
  have hS : IsCompact S := by
    have hcl : IsClosed S := by
      simpa only [Valuation.restrict_eq_one_iff] using
        (ValuativeRel.valuation F).isClosed_sphere (r := 1)
    exact (IsNonarchimedeanLocalField.isCompact_closedBall F 1).of_isClosed_subset hcl
      fun x hx => le_of_eq hx
  have he : (FML.unitGroup F : Set Fˣ) = Units.val ⁻¹' S := by
    ext a
    exact Valuation.mem_unitGroup_iff F (ValuativeRel.valuation F) a
  rw [he]
  refine Units.isEmbedding_val₀.isInducing.isCompact_preimage' hS fun x hx => ?_
  have hx0 : x ≠ 0 := by
    rintro rfl
    have hx' : ValuativeRel.valuation F (0 : F) = 1 := hx
    rw [map_zero] at hx'
    exact zero_ne_one hx'
  exact ⟨Units.mk0 x hx0, rfl⟩

/-- The order of the determinant, `g ↦ ord_F (det g)`, as a homomorphism to `ℤ`. -/
def determinantOrder : GeneralLinear n F →* Multiplicative ℤ :=
  (fieldOrderUnits F).comp GeneralLinear.determinant

theorem continuous_determinantOrder_toAdd :
    Continuous fun g : GeneralLinear n F => (determinantOrder F n g).toAdd :=
  continuous_toAdd.comp ((fieldOrderUnits_continuous F).comp
    (GeneralLinear.determinantContinuous (R := F) (n := n)).continuous)

theorem determinantOrder_scalar_mul (a : Fˣ) (g : GeneralLinear n F) :
    (determinantOrder F n (GeneralLinear.scalar a * g)).toAdd =
      n * (fieldOrderUnits F a).toAdd + (determinantOrder F n g).toAdd := by
  simp only [determinantOrder, MonoidHom.comp_apply, map_mul, toAdd_mul,
    GeneralLinear.determinant, GeneralLinear.scalar, Matrix.GeneralLinearGroup.det_scalar,
    map_pow, toAdd_pow, Fintype.card_fin, nsmul_eq_mul]

theorem isOpen_degreeWindow_determinantOrder (c : ℤ) :
    IsOpen (degreeWindow (determinantOrder F n) n c) :=
  (isOpen_discrete (Ico c (c + n))).preimage (continuous_determinantOrder_toAdd F n)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The scalar matrices are central. -/
theorem scalar_mem_center (a : Fˣ) :
    GeneralLinear.scalar a ∈ Subgroup.center (GeneralLinear n F) :=
  (GeneralLinear.scalarToCenter (n := n) a).property

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Every central element is a scalar matrix. -/
theorem exists_scalar_of_mem_center {z : GeneralLinear n F}
    (hz : z ∈ Subgroup.center (GeneralLinear n F)) : ∃ a : Fˣ, GeneralLinear.scalar a = z := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
  exact hz

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem mk_scalar_mul (a : Fˣ) (g : GeneralLinear n F) :
    (QuotientGroup.mk (GeneralLinear.scalar a * g) :
      GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F)) = QuotientGroup.mk g := by
  rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr (scalar_mem_center F n a), one_mul]

/-- If a scalar multiple `a k` of an element of a compact set `K` lies in the determinant
window, then `a` lies in a compact set of units depending only on `K`. -/
theorem exists_isCompact_scalar_of_mem_window (hn : 0 < n) {K : Set (GeneralLinear n F)}
    (hK : IsCompact K) :
    ∃ B : Set Fˣ, IsCompact B ∧ ∀ (a : Fˣ), ∀ k ∈ K,
      GeneralLinear.scalar a * k ∈ degreeWindow (determinantOrder F n) n 0 → a ∈ B := by
  classical
  let f : GeneralLinear n F → ℤ := fun g => |(determinantOrder F n g).toAdd|
  have hf : Continuous f := continuous_abs.comp (continuous_determinantOrder_toAdd F n)
  have hfin : (f '' K).Finite := (hK.image hf).finite_of_discrete
  obtain ⟨M, hM⟩ := hfin.bddAbove
  obtain ⟨ϖ, hϖ⟩ := fieldOrderUnits_surjective F (Multiplicative.ofAdd 1)
  let N : ℤ := M + n
  refine ⟨⋃ j ∈ Finset.Icc (-N) N, (fun u => ϖ ^ j * u) '' (FML.unitGroup F : Set Fˣ), ?_, ?_⟩
  · exact (Finset.Icc (-N) N).isCompact_biUnion fun j _ =>
      (isCompact_unitGroup F).image (continuous_const.mul continuous_id)
  · intro a k hk ha
    have hkM : |(determinantOrder F n k).toAdd| ≤ M := hM ⟨k, hk, rfl⟩
    have hM0 : 0 ≤ M := (abs_nonneg _).trans hkM
    have hdeg := determinantOrder_scalar_mul F n a k
    obtain ⟨h0, h1⟩ := ha
    rw [hdeg] at h0 h1
    rw [abs_le] at hkM
    have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast hn
    have hj : -N ≤ (fieldOrderUnits F a).toAdd ∧ (fieldOrderUnits F a).toAdd ≤ N := by
      constructor
      · rcases le_or_gt 0 (fieldOrderUnits F a).toAdd with hj | hj
        · linarith
        · nlinarith
      · rcases le_or_gt (fieldOrderUnits F a).toAdd 0 with hj | hj
        · linarith
        · nlinarith
    refine Set.mem_biUnion (Finset.mem_Icc.mpr hj)
      ⟨ϖ ^ (-(fieldOrderUnits F a).toAdd) * a, ?_, ?_⟩
    · rw [SetLike.mem_coe, ← fieldOrderUnits_ker, MonoidHom.mem_ker, map_mul, map_zpow, hϖ]
      apply Multiplicative.toAdd.injective
      simp
    · simp only
      group

variable [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
  [MeasurableSpace (GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F))]
  [BorelSpace (GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F))]

/-- The image in `G / Z` of a measure on `G = GL_n(F)` restricted to the window
`0 ≤ ord(det g) < n`. -/
def windowMeasure (μ : Measure (GeneralLinear n F)) :
    Measure (GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F)) :=
  (μ.restrict (degreeWindow (determinantOrder F n) n 0)).map QuotientGroup.mk

theorem windowMeasure_apply (μ : Measure (GeneralLinear n F))
    {A : Set (GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F))} (hA : MeasurableSet A) :
    windowMeasure F n μ A =
      μ (QuotientGroup.mk ⁻¹' A ∩ degreeWindow (determinantOrder F n) n 0) := by
  rw [windowMeasure, Measure.map_apply QuotientGroup.continuous_mk.measurable hA,
    Measure.restrict_apply (QuotientGroup.continuous_mk.measurable hA)]

theorem windowMeasure_isMulLeftInvariant (hn : 0 < n) (μ : Measure (GeneralLinear n F))
    [μ.IsMulLeftInvariant] : (windowMeasure F n μ).IsMulLeftInvariant := by
  obtain ⟨ϖ, hϖ⟩ := fieldOrderUnits_surjective F (Multiplicative.ofAdd 1)
  let w := determinantOrder F n
  have hs : (w (GeneralLinear.scalar ϖ)).toAdd = n := by
    have h := determinantOrder_scalar_mul F n ϖ 1
    simpa [hϖ] using h
  have hwm : Measurable fun h => (w h).toAdd :=
    (continuous_determinantOrder_toAdd F n).measurable
  refine (forall_measure_preimage_mul_iff _).mp fun q A hA => ?_
  induction q using QuotientGroup.induction_on with
  | H g =>
  have hA' : MeasurableSet
      ((fun h => (QuotientGroup.mk g : GeneralLinear n F ⧸ Subgroup.center _) * h) ⁻¹' A) :=
    measurable_const_mul _ hA
  rw [windowMeasure_apply F n μ hA', windowMeasure_apply F n μ hA]
  have hP : MeasurableSet (QuotientGroup.mk ⁻¹' A : Set (GeneralLinear n F)) :=
    QuotientGroup.continuous_mk.measurable hA
  have hD : degreeWindow w n 0 = (fun h => g * h) ⁻¹' degreeWindow w n (w g).toAdd := by
    rw [degreeWindow_mul_left, sub_self]
  change μ ((fun h => g * h) ⁻¹' (QuotientGroup.mk ⁻¹' A) ∩ degreeWindow w n 0) = _
  conv_lhs => rw [hD, ← Set.preimage_inter, measure_preimage_mul]
  refine measure_inter_degreeWindow_eq w hwm hn hs μ hP ?_ _ _
  intro k h
  simp only [Set.mem_preimage]
  rw [← map_zpow, mk_scalar_mul]

theorem windowMeasure_isHaarMeasure (hn : 0 < n) (μ : Measure (GeneralLinear n F))
    [μ.IsHaarMeasure] : (windowMeasure F n μ).IsHaarMeasure := by
  have := LocalFieldTopology.generalLinear_t2Space F n
  have := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  have := windowMeasure_isMulLeftInvariant F n hn μ
  obtain ⟨K₀, hK₀c, -⟩ := LocalFieldTopology.generalLinear_compactOpen F n univ Filter.univ_mem
  let D := degreeWindow (determinantOrder F n) n 0
  obtain ⟨B, hB, hBK⟩ := exists_isCompact_scalar_of_mem_window F n hn hK₀c
  let C := (fun p : Fˣ × GeneralLinear n F => GeneralLinear.scalar p.1 * p.2) ''
    (B ×ˢ (K₀ : Set (GeneralLinear n F)))
  have hC : IsCompact C := (hB.prod hK₀c).image
    (((GeneralLinear.scalarContinuous (R := F) (n := n)).continuous.comp continuous_fst).mul
      continuous_snd)
  have hopen : IsOpen (QuotientGroup.mk '' (K₀ : Set (GeneralLinear n F)) :
      Set (GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F))) :=
    QuotientGroup.isOpenMap_coe _ K₀.isOpen
  refine Measure.isHaarMeasure_of_isCompact_nonempty_interior _ (QuotientGroup.mk '' (K₀ : Set _))
    (hK₀c.image QuotientGroup.continuous_mk) ?_ ?_ ?_
  · rw [hopen.interior_eq]
    exact ⟨_, 1, K₀.one_mem, rfl⟩
  · rw [windowMeasure_apply F n μ hopen.measurableSet]
    refine (pos_iff_ne_zero.mp ?_)
    refine lt_of_lt_of_le ?_ (measure_mono (Set.inter_subset_inter_left _
      (Set.subset_preimage_image _ _)))
    refine (K₀.isOpen.inter (isOpen_degreeWindow_determinantOrder F n 0)).measure_pos μ
      ⟨1, K₀.one_mem, ?_⟩
    simp [degreeWindow, hn]
  · rw [windowMeasure_apply F n μ hopen.measurableSet]
    refine ne_top_of_le_ne_top hC.measure_lt_top.ne (measure_mono ?_)
    rintro g ⟨⟨k, hk, hkg⟩, hgD⟩
    obtain ⟨a, ha⟩ := exists_scalar_of_mem_center F n (QuotientGroup.eq.mp hkg)
    have hg : g = GeneralLinear.scalar a * k :=
      calc g = k * (k⁻¹ * g) := by group
        _ = k * GeneralLinear.scalar a := by rw [ha]
        _ = GeneralLinear.scalar a * k :=
          Subgroup.mem_center_iff.mp (scalar_mem_center F n a) k
    rw [hg] at hgD ⊢
    exact ⟨(a, k), ⟨hBK a k hk hgD, hk⟩, rfl⟩

end GeneralLinear

end Langlands.BaseChange
