import Langlands.Global.RankinSelberg.SchwartzBruhat
import Langlands.Global.GeneralLinearBlockIntrinsicMeasure

/-! # The covolume-one Haar measure on adelic row vectors

The measure `rectangleMeasure F 1 n` on `𝔸^n` is an additive Haar measure, the rational row
vectors `F^n` form a subgroup with a fundamental domain of measure one, and integrals over
`𝔸^n` unfold to integrals of periodizations over the compact quotient `(𝔸 / F)^n`.
-/

noncomputable section
universe u
open NumberField MeasureTheory Set
open scoped CategoryTheory.MonObj ENNReal RestrictedProduct
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.EqualAnalytic

open Langlands.Global

local instance rowSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _

local instance rowSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F]

theorem t2Space_finiteAdeles : T2Space (FiniteAdeles F) :=
  inferInstanceAs (T2Space (Πʳ v : FinitePlace F,
    [FiniteCompletion F v, v.adicCompletionIntegers F]))

omit [NumberField F] in
theorem t2Space_infiniteAdeles : T2Space (InfiniteAdeles F) :=
  inferInstanceAs (T2Space ((v : NumberField.InfinitePlace F) → v.Completion))

theorem t2Space_adeles : T2Space (Adeles F) := by
  have := t2Space_finiteAdeles F
  have := t2Space_infiniteAdeles F
  exact inferInstanceAs (T2Space (InfiniteAdeles F × FiniteAdeles F))

local instance rowT2Adeles : T2Space (Adeles F) := t2Space_adeles F

local instance rowMeasurableSpace (k m : ℕ) :
    MeasurableSpace (Matrix (Fin k) (Fin m) (Adeles F)) := borel _

local instance rowBorelSpace (k m : ℕ) :
    BorelSpace (Matrix (Fin k) (Fin m) (Adeles F)) := ⟨rfl⟩

local instance rowQuotientMeasurableSpace (k m : ℕ) :
    MeasurableSpace (Matrix (Fin k) (Fin m) (AdeleQuotient F)) := borel _

local instance rowQuotientBorelSpace (k m : ℕ) :
    BorelSpace (Matrix (Fin k) (Fin m) (AdeleQuotient F)) := ⟨rfl⟩

/-- The block unipotent subgroup whose coordinates are the row vectors. -/
abbrev RowGroup (n : ℕ) :=
  AdelicSubgroupPoints.adelicPoints F
    (GroupScheme.GeneralLinear.groupScheme (Fin (1 + n)) (CommRingCat.of F))
    (GeneralLinearBlockUnipotent.subgroup F (show 1 + n = 1 + n from rfl))

local instance rowGroupClosed (n : ℕ) :
    IsClosed (RowGroup F n : Set (AdelicGroupPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin (1 + n)) (CommRingCat.of F)))) :=
  GeneralLinearBlockUnipotent.isClosed_adelicPoints F (show 1 + n = 1 + n from rfl)

local instance rowQuotientBorel (n : ℕ) :
    BorelSpace (AdelicSubgroupPoints.RationalQuotient F
      (GroupScheme.GeneralLinear.groupScheme (Fin (1 + n)) (CommRingCat.of F))
      (GeneralLinearBlockUnipotent.subgroup F (show 1 + n = 1 + n from rfl))) :=
  AdelicSubgroupPoints.rationalQuotientBorelSpace F _ _

local instance rowGroupLocallyCompact (n : ℕ) : LocallyCompactSpace (RowGroup F n) :=
  (GeneralLinearBlockUnipotent.isClosed_adelicPoints F
    (show 1 + n = 1 + n from rfl)).locallyCompactSpace

/-- The coordinate homeomorphism of the block unipotent subgroup onto `𝔸^n`. -/
def rowHomeomorph (n : ℕ) : RowGroup F n ≃ₜ RowVector F n where
  toEquiv := (GeneralLinearBlockUnipotent.adelicCoordinates F
    (show 1 + n = 1 + n from rfl)).toEquiv.trans Multiplicative.toAdd
  continuous_toFun := continuous_toAdd.comp
    (GeneralLinearBlockUnipotent.adelicCoordinates F (show 1 + n = 1 + n from rfl)).continuous
  continuous_invFun :=
    (GeneralLinearBlockUnipotent.adelicCoordinates F
      (show 1 + n = 1 + n from rfl)).symm.continuous.comp continuous_ofAdd

theorem rowHomeomorph_apply (n : ℕ) (x : RowGroup F n) :
    rowHomeomorph F n x =
      (GeneralLinearBlockUnipotent.adelicCoordinates F (show 1 + n = 1 + n from rfl) x).toAdd :=
  rfl

theorem rowHomeomorph_mul (n : ℕ) (x y : RowGroup F n) :
    rowHomeomorph F n (x * y) = rowHomeomorph F n x + rowHomeomorph F n y := by
  simp only [rowHomeomorph_apply, map_mul, toAdd_mul]

theorem rowHomeomorph_symm_add (n : ℕ) (v w : RowVector F n) :
    (rowHomeomorph F n).symm (v + w) =
      (rowHomeomorph F n).symm v * (rowHomeomorph F n).symm w := by
  apply (rowHomeomorph F n).injective
  rw [rowHomeomorph_mul]
  simp only [Homeomorph.apply_symm_apply]

/-- The rational row vectors `F^n ⊆ 𝔸^n`. -/
def rowLattice (n : ℕ) : AddSubgroup (RowVector F n) :=
  ((diagonal F).toAddMonoidHom.mapMatrix :
    Matrix (Fin 1) (Fin n) F →+ RowVector F n).range

instance rowLattice_countable (n : ℕ) : Countable (rowLattice F n) := by
  have := numberField_countable F
  have : Countable (Matrix (Fin 1) (Fin n) F) := inferInstanceAs (Countable (Fin 1 → Fin n → F))
  have hc : (rowLattice F n : Set (RowVector F n)).Countable := by
    simpa only [rowLattice, AddMonoidHom.coe_range] using Set.countable_range
      ((diagonal F).toAddMonoidHom.mapMatrix : Matrix (Fin 1) (Fin n) F → RowVector F n)
  exact hc.to_subtype

theorem mem_rowLattice_iff (n : ℕ) (v : RowVector F n) :
    v ∈ rowLattice F n ↔ ∃ C : Matrix (Fin 1) (Fin n) F, C.map (diagonal F) = v :=
  Iff.rfl

theorem rowHomeomorph_rational (n : ℕ)
    (q : AdelicSubgroupPoints.rationalPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin (1 + n)) (CommRingCat.of F))
      (GeneralLinearBlockUnipotent.subgroup F (show 1 + n = 1 + n from rfl))) :
    rowHomeomorph F n (AdelicSubgroupPoints.rational F _ _ q) =
      ((GeneralLinearBlockUnipotent.rationalCoordinates F
        (show 1 + n = 1 + n from rfl) q).toAdd).map (diagonal F) :=
  GeneralLinearBlockUnipotent.adelicCoordinates_rational F _ q

/-- The image of the principal subgroup is the rational lattice. -/
theorem rowHomeomorph_mem_rowLattice_iff (n : ℕ) (x : RowGroup F n) :
    rowHomeomorph F n x ∈ rowLattice F n ↔
      x ∈ AdelicSubgroupPoints.rationalSubgroup F
        (GroupScheme.GeneralLinear.groupScheme (Fin (1 + n)) (CommRingCat.of F))
        (GeneralLinearBlockUnipotent.subgroup F (show 1 + n = 1 + n from rfl)) := by
  constructor
  · rintro ⟨C, hC⟩
    change C.map (diagonal F) = _ at hC
    let q := (GeneralLinearBlockUnipotent.rationalCoordinates F
      (show 1 + n = 1 + n from rfl)).symm (Multiplicative.ofAdd C)
    refine ⟨q, ?_⟩
    apply (rowHomeomorph F n).injective
    rw [rowHomeomorph_rational]
    simpa only [q, MulEquiv.apply_symm_apply, toAdd_ofAdd] using hC
  · rintro ⟨q, rfl⟩
    exact ⟨_, (rowHomeomorph_rational F n q).symm⟩

section Measure

variable [CompactSpace (AdeleQuotient F)]

omit [CompactSpace (AdeleQuotient F)] in
/-- The covolume-one measure is the image of the normalized subgroup Haar measure. -/
theorem rectangleMeasure_eq_map (n : ℕ) :
    rectangleMeasure F 1 n = Measure.map (rowHomeomorph F n)
      (GeneralLinearBlockUnipotent.normalizedBlockHaarMeasure F
        (show 1 + n = 1 + n from rfl)) :=
  rfl

omit [CompactSpace (AdeleQuotient F)] in
theorem normalizedBlockHaarMeasure_eq (n : ℕ) :
    GeneralLinearBlockUnipotent.normalizedBlockHaarMeasure F (show 1 + n = 1 + n from rfl) =
      AdelicSubgroupPoints.quotientMassNormalizer F
        (GroupScheme.GeneralLinear.groupScheme (Fin (1 + n)) (CommRingCat.of F))
        (GeneralLinearBlockUnipotent.subgroup F (show 1 + n = 1 + n from rfl)) •
        (Measure.haar : Measure (RowGroup F n)) :=
  rfl

instance rectangleMeasure_isAddHaarMeasure (n : ℕ) :
    (rectangleMeasure F 1 n).IsAddHaarMeasure := by
  set c := AdelicSubgroupPoints.quotientMassNormalizer F
    (GroupScheme.GeneralLinear.groupScheme (Fin (1 + n)) (CommRingCat.of F))
    (GeneralLinearBlockUnipotent.subgroup F (show 1 + n = 1 + n from rfl)) with hc
  have hc0 : c ≠ 0 := AdelicSubgroupPoints.quotientMassNormalizer_ne_zero F _ _
  have hct : c ≠ ∞ := AdelicSubgroupPoints.quotientMassNormalizer_ne_top F _ _
  have hmap : rectangleMeasure F 1 n =
      c • Measure.map (rowHomeomorph F n) (Measure.haar : Measure (RowGroup F n)) := by
    rw [rectangleMeasure_eq_map, normalizedBlockHaarMeasure_eq, Measure.map_smul]
    exact (rowHomeomorph F n).measurable.aemeasurable
  rw [hmap]
  have hinv : (Measure.map (rowHomeomorph F n)
      (Measure.haar : Measure (RowGroup F n))).IsAddLeftInvariant := by
    constructor
    intro v
    rw [Measure.map_map (by fun_prop) (rowHomeomorph F n).measurable]
    have heq : (fun w : RowVector F n => v + w) ∘ rowHomeomorph F n =
        rowHomeomorph F n ∘ fun x => (rowHomeomorph F n).symm v * x := by
      funext x
      simp only [Function.comp_apply, rowHomeomorph_mul, Homeomorph.apply_symm_apply]
    rw [heq, ← Measure.map_map (rowHomeomorph F n).measurable (by fun_prop),
      map_mul_left_eq_self]
  have hfin : IsFiniteMeasureOnCompacts (Measure.map (rowHomeomorph F n)
      (Measure.haar : Measure (RowGroup F n))) := by
    constructor
    intro K hK
    rw [Measure.map_apply (rowHomeomorph F n).measurable hK.measurableSet]
    exact ((rowHomeomorph F n).isCompact_preimage.mpr hK).measure_lt_top
  have hpos : (Measure.map (rowHomeomorph F n)
      (Measure.haar : Measure (RowGroup F n))).IsOpenPosMeasure := by
    constructor
    intro U hU hne
    rw [Measure.map_apply (rowHomeomorph F n).measurable hU.measurableSet]
    exact (hU.preimage (rowHomeomorph F n).continuous).measure_ne_zero _
      ((rowHomeomorph F n).surjective.nonempty_preimage.mpr hne)
  have : (Measure.map (rowHomeomorph F n)
      (Measure.haar : Measure (RowGroup F n))).IsAddHaarMeasure := ⟨⟩
  exact Measure.IsAddHaarMeasure.smul _ hc0 hct

end Measure

section FundamentalDomain

/-- The principal subgroup of the block unipotent group. -/
abbrev rowRational (n : ℕ) : Subgroup (RowGroup F n) :=
  AdelicSubgroupPoints.rationalSubgroup F
    (GroupScheme.GeneralLinear.groupScheme (Fin (1 + n)) (CommRingCat.of F))
    (GeneralLinearBlockUnipotent.subgroup F (show 1 + n = 1 + n from rfl))

theorem isDiscrete_rowRational (n : ℕ) :
    IsDiscrete (rowRational F n : Set (RowGroup F n)) :=
  AdelicSubgroupPoints.isDiscrete_rationalSubgroup F _ _

/-- The Library's Borel fundamental domain of the principal subgroup, in row coordinates. -/
def rowDomain (n : ℕ) : Set (RowVector F n) :=
  (rowHomeomorph F n).symm ⁻¹'
    LeftCosetSpace.fundamentalDomain (rowRational F n) (isDiscrete_rowRational F n)

theorem measurableSet_rowDomain (n : ℕ) : MeasurableSet (rowDomain F n) :=
  (rowHomeomorph F n).symm.measurable
    (LeftCosetSpace.measurableSet_fundamentalDomain _ _)

theorem preimage_rowDomain (n : ℕ) :
    rowHomeomorph F n ⁻¹' rowDomain F n =
      LeftCosetSpace.fundamentalDomain (rowRational F n) (isDiscrete_rowRational F n) := by
  ext x
  simp [rowDomain]

/-- Every row vector has a unique translate by `F^n` in `rowDomain`. -/
theorem existsUnique_add_mem_rowDomain (n : ℕ) (v : RowVector F n) :
    ∃! c : rowLattice F n, (c : RowVector F n) + v ∈ rowDomain F n := by
  obtain ⟨γ, hγ, huniq⟩ := LeftCosetSpace.fundamentalDomain_unique (rowRational F n)
    (isDiscrete_rowRational F n) ((rowHomeomorph F n).symm v)
  have hmem : rowHomeomorph F n (γ : RowGroup F n) ∈ rowLattice F n :=
    (rowHomeomorph_mem_rowLattice_iff F n _).mpr γ.2
  refine ⟨⟨_, hmem⟩, ?_, ?_⟩
  · change (rowHomeomorph F n).symm (rowHomeomorph F n γ + v) ∈
      LeftCosetSpace.fundamentalDomain (rowRational F n) (isDiscrete_rowRational F n)
    rw [rowHomeomorph_symm_add, Homeomorph.symm_apply_apply]
    exact hγ
  · rintro ⟨w, hw⟩ hwv
    change (rowHomeomorph F n).symm (w + v) ∈
      LeftCosetSpace.fundamentalDomain (rowRational F n) (isDiscrete_rowRational F n) at hwv
    have hw' : (rowHomeomorph F n).symm w ∈ (rowRational F n : Subgroup (RowGroup F n)) := by
      rw [← rowHomeomorph_mem_rowLattice_iff, Homeomorph.apply_symm_apply]
      exact hw
    have key := huniq ⟨_, hw'⟩ (by
      rw [rowHomeomorph_symm_add] at hwv
      exact hwv)
    apply Subtype.ext
    change w = rowHomeomorph F n γ
    rw [← key]
    simp

/-- `rowDomain` is a fundamental domain for the translation action of `F^n` on `𝔸^n`. -/
theorem isAddFundamentalDomain_rowDomain (n : ℕ) (mu : Measure (RowVector F n)) :
    IsAddFundamentalDomain (rowLattice F n) (rowDomain F n) mu := by
  apply IsAddFundamentalDomain.mk' (measurableSet_rowDomain F n).nullMeasurableSet
  intro v
  obtain ⟨c, hc, hu⟩ := existsUnique_add_mem_rowDomain F n v
  exact ⟨c, hc, fun c' hc' => hu c' hc'⟩

variable [CompactSpace (AdeleQuotient F)]

/-- The fundamental domain has measure one: `F^n \ 𝔸^n` has covolume one. -/
theorem rectangleMeasure_rowDomain (n : ℕ) :
    rectangleMeasure F 1 n (rowDomain F n) = 1 := by
  rw [rectangleMeasure_eq_map,
    Measure.map_apply (rowHomeomorph F n).measurable (measurableSet_rowDomain F n),
    preimage_rowDomain, normalizedBlockHaarMeasure_eq, Measure.smul_apply, smul_eq_mul]
  have hq : AdelicSubgroupPoints.rationalQuotientHaarMeasure F
      (GroupScheme.GeneralLinear.groupScheme (Fin (1 + n)) (CommRingCat.of F))
      (GeneralLinearBlockUnipotent.subgroup F (show 1 + n = 1 + n from rfl)) univ =
      (Measure.haar : Measure (RowGroup F n))
        (LeftCosetSpace.fundamentalDomain (rowRational F n) (isDiscrete_rowRational F n)) := by
    simp only [AdelicSubgroupPoints.rationalQuotientHaarMeasure,
      LeftCosetSpace.haarQuotientMeasure, LeftCosetSpace.discreteQuotientMeasure,
      LeftCosetSpace.quotientMeasure_univ]
  have hne := Measure.measure_univ_ne_zero.mpr
    (AdelicSubgroupPoints.rationalQuotientHaarMeasure_ne_zero F
      (GroupScheme.GeneralLinear.groupScheme (Fin (1 + n)) (CommRingCat.of F))
      (GeneralLinearBlockUnipotent.subgroup F (show 1 + n = 1 + n from rfl)))
  have := AdelicSubgroupPoints.rationalQuotientHaarMeasure_isFiniteMeasure F
      (GroupScheme.GeneralLinear.groupScheme (Fin (1 + n)) (CommRingCat.of F))
      (GeneralLinearBlockUnipotent.subgroup F (show 1 + n = 1 + n from rfl))
  have hfin := measure_ne_top (AdelicSubgroupPoints.rationalQuotientHaarMeasure F
      (GroupScheme.GeneralLinear.groupScheme (Fin (1 + n)) (CommRingCat.of F))
      (GeneralLinearBlockUnipotent.subgroup F (show 1 + n = 1 + n from rfl))) univ
  rw [AdelicSubgroupPoints.quotientMassNormalizer, ← hq]
  exact ENNReal.inv_mul_cancel hne hfin

omit [CompactSpace (AdeleQuotient F)] in
theorem continuous_matrixQuotientMap (n : ℕ) :
    Continuous (matrixQuotientMap (K := F) (a := 1) (b := n)) :=
  (isOpenQuotientMap_matrixQuotientMap (K := F) 1 n).continuous

/-- The image of the restriction to the fundamental domain is the Haar probability measure of
the compact quotient `(𝔸 / F)^n`. -/
theorem map_matrixQuotientMap_restrict (n : ℕ) :
    Measure.map (matrixQuotientMap (K := F) (a := 1) (b := n))
        ((rectangleMeasure F 1 n).restrict (rowDomain F n)) =
      matrixQuotientHaar F 1 n := by
  set c := AdelicSubgroupPoints.quotientMassNormalizer F
    (GroupScheme.GeneralLinear.groupScheme (Fin (1 + n)) (CommRingCat.of F))
    (GeneralLinearBlockUnipotent.subgroup F (show 1 + n = 1 + n from rfl))
  rw [← GeneralLinearBlockUnipotent.map_quotientHomeomorph_normalizedRationalQuotientHaarMeasure
    F (show 1 + n = 1 + n from rfl)]
  simp only [AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure,
    AdelicSubgroupPoints.rationalQuotientHaarMeasure, LeftCosetSpace.haarQuotientMeasure,
    LeftCosetSpace.discreteQuotientMeasure, LeftCosetSpace.quotientMeasure]
  rw [rectangleMeasure_eq_map, normalizedBlockHaarMeasure_eq, Measure.map_smul,
    Measure.restrict_smul, Measure.map_smul, Measure.map_smul,
    (rowHomeomorph F n).measurableEmbedding.restrict_map, preimage_rowDomain,
    Measure.map_map (continuous_matrixQuotientMap F n).measurable
      (rowHomeomorph F n).measurable,
    Measure.map_map (GeneralLinearBlockUnipotent.quotientHomeomorph F
      (show 1 + n = 1 + n from rfl)).continuous.measurable (LeftCosetSpace.measurable_mk _)]
  all_goals first
    | rfl
    | exact (GeneralLinearBlockUnipotent.quotientHomeomorph F _).continuous.measurable.aemeasurable
    | exact (continuous_matrixQuotientMap F n).measurable.aemeasurable
    | exact (rowHomeomorph F n).measurable.aemeasurable

/-- Unfolding along `F^n`: the integral of `f` over `𝔸^n` is the integral over `(𝔸 / F)^n` of
its periodization. -/
theorem integral_eq_integral_periodization (n : ℕ) (f : RowVector F n → ℂ)
    (hf : Integrable f (rectangleMeasure F 1 n))
    (P : Matrix (Fin 1) (Fin n) (AdeleQuotient F) → ℂ)
    (hP : ∀ v, HasSum (fun c : rowLattice F n => f (c + v)) (P (matrixQuotientMap v)))
    (hPm : AEStronglyMeasurable P (matrixQuotientHaar F 1 n)) :
    ∫ v, f v ∂rectangleMeasure F 1 n = ∫ x, P x ∂matrixQuotientHaar F 1 n := by
  have hfd := isAddFundamentalDomain_rowDomain F n (rectangleMeasure F 1 n)
  rw [← map_matrixQuotientMap_restrict F n] at hPm ⊢
  rw [integral_map (continuous_matrixQuotientMap F n).aemeasurable hPm]
  have h1 : ∫ v, f v ∂rectangleMeasure F 1 n =
      ∑' c : rowLattice F n, ∫ v in rowDomain F n, f (c + v) ∂rectangleMeasure F 1 n := by
    rw [hfd.integral_eq_tsum' f hf]
    exact ((Equiv.neg (rowLattice F n)).tsum_eq
      (fun c : rowLattice F n => ∫ v in rowDomain F n, f (c + v) ∂rectangleMeasure F 1 n))
  have hmeas : ∀ c : rowLattice F n, AEStronglyMeasurable (fun v => f (c + v))
      ((rectangleMeasure F 1 n).restrict (rowDomain F n)) := fun c =>
    ((hf.aestronglyMeasurable.comp_measurePreserving
      (measurePreserving_add_left (rectangleMeasure F 1 n) (c : RowVector F n)))).restrict
  have hlin : ∑' c : rowLattice F n,
      ∫⁻ v in rowDomain F n, ‖f (c + v)‖ₑ ∂rectangleMeasure F 1 n ≠ ⊤ := by
    have := hfd.lintegral_eq_tsum'' (fun v => ‖f v‖ₑ)
    simp only [AddSubgroup.vadd_def, vadd_eq_add] at this
    rw [← this]
    exact hf.hasFiniteIntegral.ne
  rw [h1, ← integral_tsum hmeas hlin]
  refine setIntegral_congr_fun (measurableSet_rowDomain F n) fun v _ => ?_
  exact (hP v).tsum_eq

/-- The nonnegative form of the unfolding along `F^n`. -/
theorem lintegral_eq_lintegral_periodization (n : ℕ) (f : RowVector F n → ℝ≥0∞)
    (hf : AEMeasurable f (rectangleMeasure F 1 n))
    (P : Matrix (Fin 1) (Fin n) (AdeleQuotient F) → ℝ≥0∞)
    (hP : ∀ v, ∑' c : rowLattice F n, f (c + v) = P (matrixQuotientMap v))
    (hPm : AEMeasurable P (matrixQuotientHaar F 1 n)) :
    ∫⁻ v, f v ∂rectangleMeasure F 1 n = ∫⁻ x, P x ∂matrixQuotientHaar F 1 n := by
  have hfd := isAddFundamentalDomain_rowDomain F n (rectangleMeasure F 1 n)
  rw [← map_matrixQuotientMap_restrict F n] at hPm ⊢
  rw [lintegral_map' hPm (continuous_matrixQuotientMap F n).aemeasurable,
    hfd.lintegral_eq_tsum'' f]
  simp only [AddSubgroup.vadd_def, vadd_eq_add]
  rw [← lintegral_tsum]
  · refine setLIntegral_congr_fun (measurableSet_rowDomain F n) fun v _ => hP v
  · intro c
    exact (hf.comp_quasiMeasurePreserving
      (measurePreserving_add_left (rectangleMeasure F 1 n)
        (c : RowVector F n)).quasiMeasurePreserving).restrict

end FundamentalDomain

end Langlands.Global.RankinSelbergGlobal.EqualAnalytic
