import Langlands.BaseChange.CentralQuotientWindowMeasure
import Langlands.BaseChange.RegularNormCentralizerAlgebra
import Langlands.BaseChange.TwistedCharacter.MatrixHaarChart
import Langlands.Analysis.Local.QuotientNormalizingFunction

/-! # Window volumes of elliptic centralizers and the Weil formula on the window -/

noncomputable section

namespace Langlands.BaseChange

open JacquetLanglands MeasureTheory Set _root_.Topology QuotientIntegration Plancherel
open scoped ENNReal

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u

section Invertibility

variable {F : Type u} [Field F] {n : ℕ}

/-- A nonzero matrix commuting with a regular elliptic element is invertible: it is a
polynomial in that element, hence lies in the field `F[X]/(charpoly)`. -/
private theorem isUnit_of_commute_regularElliptic {g : GeneralLinear n F}
    (hg : IsRegularElliptic g) {A : Matrix (Fin n) (Fin n) F}
    (hA : Commute A g.val) (hzero : A ≠ 0) : IsUnit A := by
  let : Fact (Irreducible g.val.charpoly) := ⟨hg.2⟩
  obtain ⟨v, hv⟩ := regularCyclicBasis F n g.val hg.1
  obtain ⟨c, hc⟩ := exists_sum_pow_of_commute hv hA
  let e := charpolyRootEvaluation g.val
  let a := AdjoinRoot.mk g.val.charpoly (∑ j : Fin n, Polynomial.monomial (j : ℕ) (c j))
  have he : e a = A := by
    change charpolyRootEvaluation g.val (AdjoinRoot.mk _ _) = _
    rw [charpolyRootEvaluation_mk, hc, map_sum]
    simp only [Polynomial.aeval_monomial, Algebra.smul_def]
  have ha : a ≠ 0 := fun hz => hzero (by rw [← he, hz, map_zero])
  exact he ▸ (isUnit_iff_ne_zero.mpr ha).map e.toMonoidHom

/-- Scalar matrices lie in every centralizer. -/
theorem scalar_mem_glCentralizer (g : GeneralLinear n F) (a : Fˣ) :
    GeneralLinear.scalar a ∈ glCentralizer g := by
  rw [glCentralizer_eq_centralizer]
  exact Subgroup.center_le_centralizer _ (scalar_mem_center F n a)

end Invertibility

section Compact

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}

/-- The centralizer of a regular elliptic element is a compact set times the scalars: the
compact set consists of the centralizing matrices with integral entries and one entry equal
to `1`, and every centralizing element is brought into it by dividing by an entry of largest
valuation. -/
theorem exists_isCompact_scalar_mul_glCentralizer (hn : 0 < n) (g : GeneralLinear n F)
    (hg : IsRegularElliptic g) :
    ∃ K : Set (glCentralizer g), IsCompact K ∧
      ∀ x : glCentralizer g, ∃ a : Fˣ, ∃ k ∈ K, x.val = GeneralLinear.scalar a * k.val := by
  classical
  let C := glCentralizer g
  let G := GeneralLinear n F
  let M := Matrix (Fin n) (Fin n) F
  let v := ValuativeRel.valuation F
  let : NeZero n := ⟨hn.ne'⟩
  have : T2Space F := LocalFieldTopology.t2Space F
  let B : Set M := {A | ∀ i j, v (A i j) ≤ 1}
  let D : Set M := {A | Commute A g.val ∧ ∃ ij : Fin n × Fin n, A ij.1 ij.2 = 1}
  have hB : IsCompact B := by
    exact (IsNonarchimedeanLocalField.isCompact_closedBall F 1).matrix
  have hD : IsClosed D := by
    have hComm : IsClosed {A : M | A * g.val = g.val * A} :=
      isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
    have hOne : IsClosed (⋃ ij : Fin n × Fin n, {A : M | A ij.1 ij.2 = 1}) :=
      isClosed_iUnion_of_finite fun ij => isClosed_eq
        (continuous_id.matrix_elem ij.1 ij.2) continuous_const
    convert hComm.inter hOne using 1
    ext A
    simp [D, Commute, SemiconjBy]
  let f : C → M := fun x => x.val.val
  have hf : IsEmbedding f :=
    (isOpenEmbedding_generalLinearVal F F n).isEmbedding.comp IsEmbedding.subtypeVal
  let K : Set C := f ⁻¹' (B ∩ D)
  have hK : IsCompact K := by
    refine hf.isInducing.isCompact_preimage' (hB.inter_right hD) ?_
    intro A hA
    obtain ⟨hComm, ij, hOne⟩ := hA.2
    have hne : A ≠ 0 := by
      intro heq
      have hz : A ij.1 ij.2 = 0 := congrArg (fun m : M => m ij.1 ij.2) heq
      exact zero_ne_one (hz.symm.trans hOne)
    let xu := (isUnit_of_commute_regularElliptic hg hComm hne).unit
    have hxu : xu.val = A := IsUnit.unit_spec _
    have huC : (xu : G) ∈ C := by
      change (xu : G) ∈ glCentralizer g
      rw [glCentralizer_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
      exact Units.ext (by change xu.val * g.val = g.val * xu.val; rw [hxu, hComm.eq])
    exact ⟨⟨xu, huC⟩, hxu⟩
  refine ⟨K, hK, fun x => ?_⟩
  obtain ⟨ij, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun ij : Fin n × Fin n => v (f x ij.1 ij.2)) Finset.univ_nonempty
  have ha : f x ij.1 ij.2 ≠ 0 := by
    intro hz
    apply Units.ne_zero x.val
    ext i j
    have hx := hmax (i, j) (Finset.mem_univ _)
    change v (f x i j) ≤ v (f x ij.1 ij.2) at hx
    rw [hz, map_zero] at hx
    exact v.zero_iff.mp (nonpos_iff_eq_zero.mp hx)
  let a : Fˣ := Units.mk0 (f x ij.1 ij.2) ha
  let y : C := ⟨GeneralLinear.scalar a⁻¹ * x.val,
    C.mul_mem (scalar_mem_glCentralizer g a⁻¹) x.property⟩
  have hy : f y = (a : F)⁻¹ • f x := by
    change (GeneralLinear.scalar a⁻¹ * x.val).val = _
    rw [Units.val_mul]
    change Matrix.scalar _ ((a⁻¹ : Fˣ) : F) * f x = _
    rw [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
    rfl
  refine ⟨a, y, ⟨?_, ?_⟩, ?_⟩
  · intro i j
    rw [hy]
    change v ((a : F)⁻¹ * f x i j) ≤ 1
    rw [map_mul, map_inv₀]
    have hvpos : 0 < v (a : F) := (v.ne_zero_iff.mpr a.ne_zero).bot_lt
    exact (inv_mul_le_one₀ hvpos).mpr (hmax (i, j) (Finset.mem_univ _))
  · have hyC : Commute (y : G) g := by
      apply Subgroup.mem_centralizer_singleton_iff.mp
      rw [← glCentralizer_eq_centralizer]
      exact y.property
    refine ⟨hyC.map (Units.coeHom M), ij, ?_⟩
    rw [hy]
    exact inv_mul_cancel₀ ha
  · change x.val = GeneralLinear.scalar a * (GeneralLinear.scalar a⁻¹ * x.val)
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]

end Compact

section Window

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}
  [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]

/-- The volume of the determinant window `0 ≤ ord(det h) < n` inside a subgroup. -/
def subgroupWindowVolume (H : Subgroup (GeneralLinear n F)) (μH : Measure H) : ℝ≥0∞ :=
  μH {h | h.val ∈ degreeWindow (determinantOrder F n) n 0}

/-- For a left-invariant measure on a subgroup containing the scalars, every translate
`{h | h x ∈ D}` of the determinant window has the volume of the window itself. -/
theorem measure_mul_mem_window_eq (hn : 0 < n) (H : Subgroup (GeneralLinear n F))
    (hZ : Subgroup.center (GeneralLinear n F) ≤ H) (μH : Measure H) [μH.IsMulLeftInvariant]
    (x : GeneralLinear n F) :
    μH {h | h.val * x ∈ degreeWindow (determinantOrder F n) n 0} =
      subgroupWindowVolume H μH := by
  obtain ⟨ϖ, hϖ⟩ := fieldOrderUnits_surjective F (Multiplicative.ofAdd 1)
  let w : H →* Multiplicative ℤ := (determinantOrder F n).comp H.subtype
  let s : H := ⟨GeneralLinear.scalar ϖ, hZ (scalar_mem_center F n ϖ)⟩
  have hs : (w s).toAdd = n := by
    have h := determinantOrder_scalar_mul F n ϖ 1
    simpa [hϖ, w, s] using h
  have hwm : Measurable fun h => (w h).toAdd :=
    ((continuous_determinantOrder_toAdd F n).comp continuous_subtype_val).measurable
  have h1 : {h : H | h.val * x ∈ degreeWindow (determinantOrder F n) n 0} =
      univ ∩ degreeWindow w n (-(determinantOrder F n x).toAdd) := by
    ext h
    simp only [degreeWindow, mem_ofPred_eq, map_mul, toAdd_mul, univ_inter, w,
      MonoidHom.comp_apply, Subgroup.coe_subtype]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> omega
  have h2 : {h : H | h.val ∈ degreeWindow (determinantOrder F n) n 0} =
      univ ∩ degreeWindow w n 0 := by
    rw [univ_inter]
    rfl
  rw [subgroupWindowVolume, h1, h2]
  exact measure_inter_degreeWindow_eq w hwm hn hs μH MeasurableSet.univ (fun _ _ => Iff.rfl) _ _

omit [BorelSpace (GeneralLinear n F)] in
/-- The window of a subgroup has positive volume for a Haar measure. -/
theorem subgroupWindowVolume_pos (hn : 0 < n) (H : Subgroup (GeneralLinear n F))
    (μH : Measure H) [μH.IsOpenPosMeasure] : 0 < subgroupWindowVolume H μH := by
  refine ((isOpen_degreeWindow_determinantOrder F n 0).preimage
    continuous_subtype_val).measure_pos μH ⟨1, ?_⟩
  simp [degreeWindow, hn]

omit [BorelSpace (GeneralLinear n F)] in
/-- The window of the centralizer of a regular elliptic element has finite volume. -/
theorem subgroupWindowVolume_lt_top (hn : 0 < n) (g : GeneralLinear n F)
    (hg : IsRegularElliptic g) (H : Subgroup (GeneralLinear n F)) (hH : glCentralizer g = H)
    (μH : Measure H) [IsFiniteMeasureOnCompacts μH] :
    subgroupWindowVolume H μH < ∞ := by
  subst hH
  obtain ⟨K, hK, hcover⟩ := exists_isCompact_scalar_mul_glCentralizer hn g hg
  obtain ⟨B, hB, hBK⟩ := exists_isCompact_scalar_of_mem_window F n hn
    (hK.image continuous_subtype_val)
  let Φ : Fˣ × glCentralizer g → glCentralizer g :=
    fun p => ⟨GeneralLinear.scalar p.1, scalar_mem_glCentralizer g p.1⟩ * p.2
  have hΦ : Continuous Φ := by
    refine (Continuous.subtype_mk ?_ _).mul continuous_snd
    exact (GeneralLinear.scalarContinuous (R := F) (n := n)).continuous.comp continuous_fst
  refine lt_of_le_of_lt (measure_mono ?_) ((hB.prod hK).image hΦ).measure_lt_top
  intro h hh
  obtain ⟨a, k, hk, hak⟩ := hcover h
  have hD : GeneralLinear.scalar a * k.val ∈ degreeWindow (determinantOrder F n) n 0 := by
    rw [← hak]
    exact hh
  exact ⟨(a, k), ⟨hBK a k.val ⟨k, hk, rfl⟩ hD, hk⟩, Subtype.ext hak.symm⟩

/-- **Weil's formula on the determinant window.** Let `H` be a closed subgroup of `G = GL_n(F)`
containing the scalars, with a measure `μH` that is left and right invariant, and let `ν` be a
quotient measure on `H \ G` compatible with `μG` and `μH`. Then for every measurable set `C` of
cosets, the window part of its preimage in `G` has `μG`-volume `vol(H ∩ D) · ν C`. -/
theorem measure_preimage_inter_window_eq (hn : 0 < n) (H : Subgroup (GeneralLinear n F))
    (hH : IsClosed (H : Set (GeneralLinear n F)))
    (hZ : Subgroup.center (GeneralLinear n F) ≤ H)
    (μG : Measure (GeneralLinear n F)) [IsFiniteMeasureOnCompacts μG]
    (μH : Measure H) [μH.IsMulLeftInvariant] [μH.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μH] (ν : Measure (LeftQuotient H))
    (hν : IsCompatible H μG μH ν) {C : Set (LeftQuotient H)} (hC : MeasurableSet C) :
    μG (leftQuotientMap H ⁻¹' C ∩ degreeWindow (determinantOrder F n) n 0) =
      subgroupWindowVolume H μH * ν C := by
  have := LocalFieldTopology.generalLinear_t2Space F n
  have := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  have := LocalFieldTopology.generalLinear_secondCountableTopology F n
  let D := degreeWindow (determinantOrder F n) n 0
  have hDm : MeasurableSet D := (isOpen_degreeWindow_determinantOrder F n 0).measurableSet
  have hPm : MeasurableSet (leftQuotientMap H ⁻¹' C) :=
    (leftQuotient_isOpenQuotientMap H).continuous.measurable hC
  rw [← lintegral_indicator_one (hPm.inter hDm),
    hν.lintegral_eq_lintegral_quotientAverageENNReal hH _
      (measurable_one.indicator (hPm.inter hDm)),
    ← lintegral_indicator_one hC, ← lintegral_const_mul _ (measurable_one.indicator hC)]
  refine lintegral_congr fun q => ?_
  induction q using Quotient.inductionOn with
  | h x =>
  rw [quotientAverageENNReal_mk]
  have hmk (h : H) : leftQuotientMap H (h.val * x) = leftQuotientMap H x := by
    apply Quotient.sound
    change QuotientGroup.rightRel H (h.val * x) x
    rw [QuotientGroup.rightRel_apply]
    simp [mul_inv_rev]
  have hind (h : H) : (leftQuotientMap H ⁻¹' C ∩ D).indicator 1 (h.val * x) =
      C.indicator (1 : LeftQuotient H → ℝ≥0∞) (Quotient.mk _ x) *
        D.indicator 1 (h.val * x) := by
    by_cases hc : Quotient.mk _ x ∈ C
    · have hc' : leftQuotientMap H (h.val * x) ∈ C := by rw [hmk]; exact hc
      by_cases hd : h.val * x ∈ D
      · simp [indicator_of_mem (show h.val * x ∈ leftQuotientMap H ⁻¹' C ∩ D from ⟨hc', hd⟩),
          indicator_of_mem hc, indicator_of_mem hd]
      · rw [indicator_of_notMem (fun hm => hd hm.2), indicator_of_notMem hd, mul_zero]
    · have hc' : leftQuotientMap H (h.val * x) ∉ C := by rw [hmk]; exact hc
      rw [indicator_of_notMem (fun hm => hc' hm.1), indicator_of_notMem hc, zero_mul]
  simp_rw [hind]
  have hDx : Measurable fun h : H => D.indicator (1 : GeneralLinear n F → ℝ≥0∞) (h.val * x) :=
    (measurable_one.indicator hDm).comp (continuous_subtype_val.mul continuous_const).measurable
  rw [lintegral_const_mul _ hDx, mul_comm]
  congr 1
  have hset : MeasurableSet {h : H | h.val * x ∈ D} :=
    hDm.preimage (continuous_subtype_val.mul continuous_const).measurable
  rw [← measure_mul_mem_window_eq hn H hZ μH x, ← lintegral_indicator_one hset]
  rfl

end Window

end Langlands.BaseChange
