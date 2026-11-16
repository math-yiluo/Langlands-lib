import Langlands.Global.RankinSelberg.DualExpansionBridge
import Langlands.Global.RankinSelberg.EqualAnalyticRowMeasure

/-! # The covolume-one Haar measure on adelic rectangular matrices

The measure `rectangleMeasure F k m` on `M_{k×m}(𝔸)` is an additive Haar measure, the rational
matrices `M_{k×m}(F)` have a fundamental domain of measure one, and integrals over `M_{k×m}(𝔸)`
unfold to integrals of periodizations over the compact quotient `M_{k×m}(𝔸 / F)`. This is the
rectangular version of the Library module `EqualAnalyticRowMeasure` (the case `k = 1`), with the
same proofs.
-/

noncomputable section
universe u
open NumberField MeasureTheory Set
open scoped CategoryTheory.MonObj ENNReal RestrictedProduct
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global

local instance rectSchemeAffine' (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _

local instance rectSchemeSmooth' (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F]

local instance rectT2Adeles' : T2Space (Adeles F) := EqualAnalytic.t2Space_adeles F

local instance rectMeasurableSpace' (k m : ℕ) :
    MeasurableSpace (Matrix (Fin k) (Fin m) (Adeles F)) := borel _

local instance rectBorelSpace' (k m : ℕ) :
    BorelSpace (Matrix (Fin k) (Fin m) (Adeles F)) := ⟨rfl⟩

local instance rectQuotientMeasurableSpace' (k m : ℕ) :
    MeasurableSpace (Matrix (Fin k) (Fin m) (AdeleQuotient F)) := borel _

local instance rectQuotientBorelSpace' (k m : ℕ) :
    BorelSpace (Matrix (Fin k) (Fin m) (AdeleQuotient F)) := ⟨rfl⟩

/-- The block unipotent subgroup whose coordinates are the row vectors. -/
abbrev RectGroup (k m : ℕ) :=
  AdelicSubgroupPoints.adelicPoints F
    (GroupScheme.GeneralLinear.groupScheme (Fin (k + m)) (CommRingCat.of F))
    (GeneralLinearBlockUnipotent.subgroup F (show k + m = k + m from rfl))

local instance rectGroupClosed' (k m : ℕ) :
    IsClosed (RectGroup F k m : Set (AdelicGroupPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin (k + m)) (CommRingCat.of F)))) :=
  GeneralLinearBlockUnipotent.isClosed_adelicPoints F (show k + m = k + m from rfl)

local instance rectQuotientBorel' (k m : ℕ) :
    BorelSpace (AdelicSubgroupPoints.RationalQuotient F
      (GroupScheme.GeneralLinear.groupScheme (Fin (k + m)) (CommRingCat.of F))
      (GeneralLinearBlockUnipotent.subgroup F (show k + m = k + m from rfl))) :=
  AdelicSubgroupPoints.rationalQuotientBorelSpace F _ _

local instance rectGroupLocallyCompact' (k m : ℕ) : LocallyCompactSpace (RectGroup F k m) :=
  (GeneralLinearBlockUnipotent.isClosed_adelicPoints F
    (show k + m = k + m from rfl)).locallyCompactSpace

/-- The coordinate homeomorphism of the block unipotent subgroup onto `𝔸^n`. -/
def rectHomeomorph (k m : ℕ) : RectGroup F k m ≃ₜ Matrix (Fin k) (Fin m) (Adeles F) where
  toEquiv := (GeneralLinearBlockUnipotent.adelicCoordinates F
    (show k + m = k + m from rfl)).toEquiv.trans Multiplicative.toAdd
  continuous_toFun := continuous_toAdd.comp
    (GeneralLinearBlockUnipotent.adelicCoordinates F (show k + m = k + m from rfl)).continuous
  continuous_invFun :=
    (GeneralLinearBlockUnipotent.adelicCoordinates F
      (show k + m = k + m from rfl)).symm.continuous.comp continuous_ofAdd

theorem rectHomeomorph_apply (k m : ℕ) (x : RectGroup F k m) :
    rectHomeomorph F k m x =
      (GeneralLinearBlockUnipotent.adelicCoordinates F (show k + m = k + m from rfl) x).toAdd :=
  rfl

theorem rectHomeomorph_mul (k m : ℕ) (x y : RectGroup F k m) :
    rectHomeomorph F k m (x * y) = rectHomeomorph F k m x + rectHomeomorph F k m y := by
  simp only [rectHomeomorph_apply, map_mul, toAdd_mul]

theorem rectHomeomorph_symm_add (k m : ℕ) (v w : Matrix (Fin k) (Fin m) (Adeles F)) :
    (rectHomeomorph F k m).symm (v + w) =
      (rectHomeomorph F k m).symm v * (rectHomeomorph F k m).symm w := by
  apply (rectHomeomorph F k m).injective
  rw [rectHomeomorph_mul]
  simp only [Homeomorph.apply_symm_apply]

/-- The rational row vectors `F^n ⊆ 𝔸^n`. -/
def rectLattice (k m : ℕ) : AddSubgroup (Matrix (Fin k) (Fin m) (Adeles F)) :=
  ((diagonal F).toAddMonoidHom.mapMatrix :
    Matrix (Fin k) (Fin m) F →+ Matrix (Fin k) (Fin m) (Adeles F)).range

instance rectLattice_countable (k m : ℕ) : Countable (rectLattice F k m) := by
  have := numberField_countable F
  have : Countable (Matrix (Fin k) (Fin m) F) := inferInstanceAs (Countable (Fin k → Fin m → F))
  have hc : (rectLattice F k m : Set (Matrix (Fin k) (Fin m) (Adeles F))).Countable := by
    simpa only [rectLattice, AddMonoidHom.coe_range] using Set.countable_range
      ((diagonal F).toAddMonoidHom.mapMatrix : Matrix (Fin k) (Fin m) F → Matrix (Fin k) (Fin m) (Adeles F))
  exact hc.to_subtype

theorem mem_rectLattice_iff (k m : ℕ) (v : Matrix (Fin k) (Fin m) (Adeles F)) :
    v ∈ rectLattice F k m ↔ ∃ C : Matrix (Fin k) (Fin m) F, C.map (diagonal F) = v :=
  Iff.rfl

theorem rectHomeomorph_rational (k m : ℕ)
    (q : AdelicSubgroupPoints.rationalPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin (k + m)) (CommRingCat.of F))
      (GeneralLinearBlockUnipotent.subgroup F (show k + m = k + m from rfl))) :
    rectHomeomorph F k m (AdelicSubgroupPoints.rational F _ _ q) =
      ((GeneralLinearBlockUnipotent.rationalCoordinates F
        (show k + m = k + m from rfl) q).toAdd).map (diagonal F) :=
  GeneralLinearBlockUnipotent.adelicCoordinates_rational F _ q

/-- The image of the principal subgroup is the rational lattice. -/
theorem rectHomeomorph_mem_rectLattice_iff (k m : ℕ) (x : RectGroup F k m) :
    rectHomeomorph F k m x ∈ rectLattice F k m ↔
      x ∈ AdelicSubgroupPoints.rationalSubgroup F
        (GroupScheme.GeneralLinear.groupScheme (Fin (k + m)) (CommRingCat.of F))
        (GeneralLinearBlockUnipotent.subgroup F (show k + m = k + m from rfl)) := by
  constructor
  · rintro ⟨C, hC⟩
    change C.map (diagonal F) = _ at hC
    let q := (GeneralLinearBlockUnipotent.rationalCoordinates F
      (show k + m = k + m from rfl)).symm (Multiplicative.ofAdd C)
    refine ⟨q, ?_⟩
    apply (rectHomeomorph F k m).injective
    rw [rectHomeomorph_rational]
    simpa only [q, MulEquiv.apply_symm_apply, toAdd_ofAdd] using hC
  · rintro ⟨q, rfl⟩
    exact ⟨_, (rectHomeomorph_rational F k m q).symm⟩

section Measure

variable [CompactSpace (AdeleQuotient F)]

omit [CompactSpace (AdeleQuotient F)] in
/-- The covolume-one measure is the image of the normalized subgroup Haar measure. -/
theorem rectangleMeasure_eq_map' (k m : ℕ) :
    rectangleMeasure F k m = Measure.map (rectHomeomorph F k m)
      (GeneralLinearBlockUnipotent.normalizedBlockHaarMeasure F
        (show k + m = k + m from rfl)) :=
  rfl

omit [CompactSpace (AdeleQuotient F)] in
theorem normalizedBlockHaarMeasure_eq' (k m : ℕ) :
    GeneralLinearBlockUnipotent.normalizedBlockHaarMeasure F (show k + m = k + m from rfl) =
      AdelicSubgroupPoints.quotientMassNormalizer F
        (GroupScheme.GeneralLinear.groupScheme (Fin (k + m)) (CommRingCat.of F))
        (GeneralLinearBlockUnipotent.subgroup F (show k + m = k + m from rfl)) •
        (Measure.haar : Measure (RectGroup F k m)) :=
  rfl

instance rectangleMeasure_isAddHaarMeasure' (k m : ℕ) :
    (rectangleMeasure F k m).IsAddHaarMeasure := by
  set c := AdelicSubgroupPoints.quotientMassNormalizer F
    (GroupScheme.GeneralLinear.groupScheme (Fin (k + m)) (CommRingCat.of F))
    (GeneralLinearBlockUnipotent.subgroup F (show k + m = k + m from rfl)) with hc
  have hc0 : c ≠ 0 := AdelicSubgroupPoints.quotientMassNormalizer_ne_zero F _ _
  have hct : c ≠ ∞ := AdelicSubgroupPoints.quotientMassNormalizer_ne_top F _ _
  have hmap : rectangleMeasure F k m =
      c • Measure.map (rectHomeomorph F k m) (Measure.haar : Measure (RectGroup F k m)) := by
    rw [rectangleMeasure_eq_map', normalizedBlockHaarMeasure_eq', Measure.map_smul]
    exact (rectHomeomorph F k m).measurable.aemeasurable
  rw [hmap]
  have hinv : (Measure.map (rectHomeomorph F k m)
      (Measure.haar : Measure (RectGroup F k m))).IsAddLeftInvariant := by
    constructor
    intro v
    rw [Measure.map_map (by fun_prop) (rectHomeomorph F k m).measurable]
    have heq : (fun w : Matrix (Fin k) (Fin m) (Adeles F) => v + w) ∘ rectHomeomorph F k m =
        rectHomeomorph F k m ∘ fun x => (rectHomeomorph F k m).symm v * x := by
      funext x
      simp only [Function.comp_apply, rectHomeomorph_mul, Homeomorph.apply_symm_apply]
    rw [heq, ← Measure.map_map (rectHomeomorph F k m).measurable (by fun_prop),
      map_mul_left_eq_self]
  have hfin : IsFiniteMeasureOnCompacts (Measure.map (rectHomeomorph F k m)
      (Measure.haar : Measure (RectGroup F k m))) := by
    constructor
    intro K hK
    rw [Measure.map_apply (rectHomeomorph F k m).measurable hK.measurableSet]
    exact ((rectHomeomorph F k m).isCompact_preimage.mpr hK).measure_lt_top
  have hpos : (Measure.map (rectHomeomorph F k m)
      (Measure.haar : Measure (RectGroup F k m))).IsOpenPosMeasure := by
    constructor
    intro U hU hne
    rw [Measure.map_apply (rectHomeomorph F k m).measurable hU.measurableSet]
    exact (hU.preimage (rectHomeomorph F k m).continuous).measure_ne_zero _
      ((rectHomeomorph F k m).surjective.nonempty_preimage.mpr hne)
  have : (Measure.map (rectHomeomorph F k m)
      (Measure.haar : Measure (RectGroup F k m))).IsAddHaarMeasure := ⟨⟩
  exact Measure.IsAddHaarMeasure.smul _ hc0 hct

end Measure

section FundamentalDomain

/-- The principal subgroup of the block unipotent group. -/
abbrev rectRational (k m : ℕ) : Subgroup (RectGroup F k m) :=
  AdelicSubgroupPoints.rationalSubgroup F
    (GroupScheme.GeneralLinear.groupScheme (Fin (k + m)) (CommRingCat.of F))
    (GeneralLinearBlockUnipotent.subgroup F (show k + m = k + m from rfl))

theorem isDiscrete_rectRational (k m : ℕ) :
    IsDiscrete (rectRational F k m : Set (RectGroup F k m)) :=
  AdelicSubgroupPoints.isDiscrete_rationalSubgroup F _ _

/-- The Library's Borel fundamental domain of the principal subgroup, in row coordinates. -/
def rectDomain (k m : ℕ) : Set (Matrix (Fin k) (Fin m) (Adeles F)) :=
  (rectHomeomorph F k m).symm ⁻¹'
    LeftCosetSpace.fundamentalDomain (rectRational F k m) (isDiscrete_rectRational F k m)

theorem measurableSet_rectDomain (k m : ℕ) : MeasurableSet (rectDomain F k m) :=
  (rectHomeomorph F k m).symm.measurable
    (LeftCosetSpace.measurableSet_fundamentalDomain _ _)

theorem preimage_rectDomain (k m : ℕ) :
    rectHomeomorph F k m ⁻¹' rectDomain F k m =
      LeftCosetSpace.fundamentalDomain (rectRational F k m) (isDiscrete_rectRational F k m) := by
  ext x
  simp [rectDomain]

/-- Every row vector has a unique translate by `F^n` in `rowDomain`. -/
theorem existsUnique_add_mem_rectDomain (k m : ℕ) (v : Matrix (Fin k) (Fin m) (Adeles F)) :
    ∃! c : rectLattice F k m, (c : Matrix (Fin k) (Fin m) (Adeles F)) + v ∈ rectDomain F k m := by
  obtain ⟨g₀, hg₀, huniq⟩ := LeftCosetSpace.fundamentalDomain_unique (rectRational F k m)
    (isDiscrete_rectRational F k m) ((rectHomeomorph F k m).symm v)
  have hmem : rectHomeomorph F k m (g₀ : RectGroup F k m) ∈ rectLattice F k m :=
    (rectHomeomorph_mem_rectLattice_iff F k m _).mpr g₀.2
  refine ⟨⟨_, hmem⟩, ?_, ?_⟩
  · change (rectHomeomorph F k m).symm (rectHomeomorph F k m g₀ + v) ∈
      LeftCosetSpace.fundamentalDomain (rectRational F k m) (isDiscrete_rectRational F k m)
    rw [rectHomeomorph_symm_add, Homeomorph.symm_apply_apply]
    exact hg₀
  · rintro ⟨w, hw⟩ hwv
    change (rectHomeomorph F k m).symm (w + v) ∈
      LeftCosetSpace.fundamentalDomain (rectRational F k m) (isDiscrete_rectRational F k m) at hwv
    have hw' : (rectHomeomorph F k m).symm w ∈ (rectRational F k m : Subgroup (RectGroup F k m)) := by
      rw [← rectHomeomorph_mem_rectLattice_iff, Homeomorph.apply_symm_apply]
      exact hw
    have key := huniq ⟨_, hw'⟩ (by
      rw [rectHomeomorph_symm_add] at hwv
      exact hwv)
    apply Subtype.ext
    change w = rectHomeomorph F k m g₀
    rw [← key]
    simp

/-- `rowDomain` is a fundamental domain for the translation action of `F^n` on `𝔸^n`. -/
theorem isAddFundamentalDomain_rectDomain (k m : ℕ) (mu : Measure (Matrix (Fin k) (Fin m) (Adeles F))) :
    IsAddFundamentalDomain (rectLattice F k m) (rectDomain F k m) mu := by
  apply IsAddFundamentalDomain.mk' (measurableSet_rectDomain F k m).nullMeasurableSet
  intro v
  obtain ⟨c, hc, hu⟩ := existsUnique_add_mem_rectDomain F k m v
  exact ⟨c, hc, fun c' hc' => hu c' hc'⟩

variable [CompactSpace (AdeleQuotient F)]

/-- The fundamental domain has measure one: `F^n \ 𝔸^n` has covolume one. -/
theorem rectangleMeasure_rectDomain (k m : ℕ) :
    rectangleMeasure F k m (rectDomain F k m) = 1 := by
  rw [rectangleMeasure_eq_map',
    Measure.map_apply (rectHomeomorph F k m).measurable (measurableSet_rectDomain F k m),
    preimage_rectDomain, normalizedBlockHaarMeasure_eq', Measure.smul_apply, smul_eq_mul]
  have hq : AdelicSubgroupPoints.rationalQuotientHaarMeasure F
      (GroupScheme.GeneralLinear.groupScheme (Fin (k + m)) (CommRingCat.of F))
      (GeneralLinearBlockUnipotent.subgroup F (show k + m = k + m from rfl)) univ =
      (Measure.haar : Measure (RectGroup F k m))
        (LeftCosetSpace.fundamentalDomain (rectRational F k m) (isDiscrete_rectRational F k m)) := by
    simp only [AdelicSubgroupPoints.rationalQuotientHaarMeasure,
      LeftCosetSpace.haarQuotientMeasure, LeftCosetSpace.discreteQuotientMeasure,
      LeftCosetSpace.quotientMeasure_univ]
  have hne := Measure.measure_univ_ne_zero.mpr
    (AdelicSubgroupPoints.rationalQuotientHaarMeasure_ne_zero F
      (GroupScheme.GeneralLinear.groupScheme (Fin (k + m)) (CommRingCat.of F))
      (GeneralLinearBlockUnipotent.subgroup F (show k + m = k + m from rfl)))
  have := AdelicSubgroupPoints.rationalQuotientHaarMeasure_isFiniteMeasure F
      (GroupScheme.GeneralLinear.groupScheme (Fin (k + m)) (CommRingCat.of F))
      (GeneralLinearBlockUnipotent.subgroup F (show k + m = k + m from rfl))
  have hfin := measure_ne_top (AdelicSubgroupPoints.rationalQuotientHaarMeasure F
      (GroupScheme.GeneralLinear.groupScheme (Fin (k + m)) (CommRingCat.of F))
      (GeneralLinearBlockUnipotent.subgroup F (show k + m = k + m from rfl))) univ
  rw [AdelicSubgroupPoints.quotientMassNormalizer, ← hq]
  exact ENNReal.inv_mul_cancel hne hfin

omit [CompactSpace (AdeleQuotient F)] in
theorem continuous_matrixQuotientMap' (k m : ℕ) :
    Continuous (matrixQuotientMap (K := F) (a := k) (b := m)) :=
  (isOpenQuotientMap_matrixQuotientMap (K := F) k m).continuous

/-- The image of the restriction to the fundamental domain is the Haar probability measure of
the compact quotient `(𝔸 / F)^n`. -/
theorem map_matrixQuotientMap_restrict' (k m : ℕ) :
    Measure.map (matrixQuotientMap (K := F) (a := k) (b := m))
        ((rectangleMeasure F k m).restrict (rectDomain F k m)) =
      matrixQuotientHaar F k m := by
  set c := AdelicSubgroupPoints.quotientMassNormalizer F
    (GroupScheme.GeneralLinear.groupScheme (Fin (k + m)) (CommRingCat.of F))
    (GeneralLinearBlockUnipotent.subgroup F (show k + m = k + m from rfl))
  rw [← GeneralLinearBlockUnipotent.map_quotientHomeomorph_normalizedRationalQuotientHaarMeasure
    F (show k + m = k + m from rfl)]
  simp only [AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure,
    AdelicSubgroupPoints.rationalQuotientHaarMeasure, LeftCosetSpace.haarQuotientMeasure,
    LeftCosetSpace.discreteQuotientMeasure, LeftCosetSpace.quotientMeasure]
  rw [rectangleMeasure_eq_map', normalizedBlockHaarMeasure_eq', Measure.map_smul,
    Measure.restrict_smul, Measure.map_smul, Measure.map_smul,
    (rectHomeomorph F k m).measurableEmbedding.restrict_map, preimage_rectDomain,
    Measure.map_map (continuous_matrixQuotientMap' F k m).measurable
      (rectHomeomorph F k m).measurable,
    Measure.map_map (GeneralLinearBlockUnipotent.quotientHomeomorph F
      (show k + m = k + m from rfl)).continuous.measurable (LeftCosetSpace.measurable_mk _)]
  all_goals first
    | rfl
    | exact (GeneralLinearBlockUnipotent.quotientHomeomorph F _).continuous.measurable.aemeasurable
    | exact (continuous_matrixQuotientMap' F k m).measurable.aemeasurable
    | exact (rectHomeomorph F k m).measurable.aemeasurable

/-- Unfolding along `F^n`: the integral of `f` over `𝔸^n` is the integral over `(𝔸 / F)^n` of
its periodization. -/
theorem integral_eq_integral_periodization' (k m : ℕ) (f : Matrix (Fin k) (Fin m) (Adeles F) → ℂ)
    (hf : Integrable f (rectangleMeasure F k m))
    (P : Matrix (Fin k) (Fin m) (AdeleQuotient F) → ℂ)
    (hP : ∀ v, HasSum (fun c : rectLattice F k m => f (c + v)) (P (matrixQuotientMap v)))
    (hPm : AEStronglyMeasurable P (matrixQuotientHaar F k m)) :
    ∫ v, f v ∂rectangleMeasure F k m = ∫ x, P x ∂matrixQuotientHaar F k m := by
  have hfd := isAddFundamentalDomain_rectDomain F k m (rectangleMeasure F k m)
  rw [← map_matrixQuotientMap_restrict' F k m] at hPm ⊢
  rw [integral_map (continuous_matrixQuotientMap' F k m).aemeasurable hPm]
  have h1 : ∫ v, f v ∂rectangleMeasure F k m =
      ∑' c : rectLattice F k m, ∫ v in rectDomain F k m, f (c + v) ∂rectangleMeasure F k m := by
    rw [hfd.integral_eq_tsum' f hf]
    exact ((Equiv.neg (rectLattice F k m)).tsum_eq
      (fun c : rectLattice F k m => ∫ v in rectDomain F k m, f (c + v) ∂rectangleMeasure F k m))
  have hmeas : ∀ c : rectLattice F k m, AEStronglyMeasurable (fun v => f (c + v))
      ((rectangleMeasure F k m).restrict (rectDomain F k m)) := fun c =>
    ((hf.aestronglyMeasurable.comp_measurePreserving
      (measurePreserving_add_left (rectangleMeasure F k m) (c : Matrix (Fin k) (Fin m) (Adeles F))))).restrict
  have hlin : ∑' c : rectLattice F k m,
      ∫⁻ v in rectDomain F k m, ‖f (c + v)‖ₑ ∂rectangleMeasure F k m ≠ ⊤ := by
    have := hfd.lintegral_eq_tsum'' (fun v => ‖f v‖ₑ)
    simp only [AddSubgroup.vadd_def, vadd_eq_add] at this
    rw [← this]
    exact hf.hasFiniteIntegral.ne
  rw [h1, ← integral_tsum hmeas hlin]
  refine setIntegral_congr_fun (measurableSet_rectDomain F k m) fun v _ => ?_
  exact (hP v).tsum_eq

/-- The nonnegative form of the unfolding along `F^n`. -/
theorem lintegral_eq_lintegral_periodization' (k m : ℕ) (f : Matrix (Fin k) (Fin m) (Adeles F) → ℝ≥0∞)
    (hf : AEMeasurable f (rectangleMeasure F k m))
    (P : Matrix (Fin k) (Fin m) (AdeleQuotient F) → ℝ≥0∞)
    (hP : ∀ v, ∑' c : rectLattice F k m, f (c + v) = P (matrixQuotientMap v))
    (hPm : AEMeasurable P (matrixQuotientHaar F k m)) :
    ∫⁻ v, f v ∂rectangleMeasure F k m = ∫⁻ x, P x ∂matrixQuotientHaar F k m := by
  have hfd := isAddFundamentalDomain_rectDomain F k m (rectangleMeasure F k m)
  rw [← map_matrixQuotientMap_restrict' F k m] at hPm ⊢
  rw [lintegral_map' hPm (continuous_matrixQuotientMap' F k m).aemeasurable,
    hfd.lintegral_eq_tsum'' f]
  simp only [AddSubgroup.vadd_def, vadd_eq_add]
  rw [← lintegral_tsum]
  · refine setLIntegral_congr_fun (measurableSet_rectDomain F k m) fun v _ => hP v
  · intro c
    exact (hf.comp_quasiMeasurePreserving
      (measurePreserving_add_left (rectangleMeasure F k m)
        (c : Matrix (Fin k) (Fin m) (Adeles F))).quasiMeasurePreserving).restrict

end FundamentalDomain

section Torus

open scoped Langlands.Automorphic.CuspidalWhittaker
open Langlands.Automorphic.CuspidalWhittaker (IsPeriodic torusLift torusMk torusHaar
  torusMk_torusLift)

/-- Uncurrying matrices over `𝔸 / F`. -/
def matrixUncurry (k m : ℕ) :
    Matrix (Fin k) (Fin m) (AdeleQuotient F) ≃ₜ+ (Fin k × Fin m → AdeleQuotient F) where
  toFun M p := M p.1 p.2
  invFun t i j := t (i, j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  continuous_toFun := continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1)
  continuous_invFun := continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)

variable [CompactSpace (AdeleQuotient F)]

local instance rectQuotientHaarIsAddHaar (k m : ℕ) :
    (matrixQuotientHaar F k m).IsAddHaarMeasure :=
  matrixQuotientHaar_isAddHaarMeasure F k m

local instance rectQuotientHaarIsProbability (k m : ℕ) :
    IsProbabilityMeasure (matrixQuotientHaar F k m) :=
  ⟨matrixQuotientHaar_univ F k m⟩

theorem measurePreserving_matrixUncurry (k m : ℕ) :
    MeasurePreserving (matrixUncurry F k m) (matrixQuotientHaar F k m)
      (torusHaar F (Fin k × Fin m)) :=
  Langlands.Automorphic.CuspidalWhittaker.measurePreserving_continuousAddEquiv _ _ _

/-- Integrals of periodic functions over the fundamental domain are torus integrals. -/
theorem setIntegral_rectDomain_eq_torusIntegral (k m : ℕ)
    (G : (Fin k × Fin m → Adeles F) → ℂ) (hG : IsPeriodic G) (hGc : Continuous G) :
    ∫ v in rectDomain F k m, G (fun p => v p.1 p.2) ∂rectangleMeasure F k m =
      Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin k × Fin m) G := by
  have hH : Continuous fun t : Fin k × Fin m → AdeleQuotient F => G (torusLift t) :=
    hG.continuous_lift hGc
  have h1 : ∀ v : Matrix (Fin k) (Fin m) (Adeles F), G (fun p => v p.1 p.2) =
      G (torusLift (matrixUncurry F k m (matrixQuotientMap v))) := by
    intro v
    apply hG.eq_of_torusMk_eq
    rw [torusMk_torusLift]
    rfl
  simp_rw [h1]
  have hGt : Continuous fun x : Matrix (Fin k) (Fin m) (AdeleQuotient F) =>
      G (torusLift (matrixUncurry F k m x)) := hH.comp (matrixUncurry F k m).continuous
  rw [← integral_map (continuous_matrixQuotientMap' F k m).aemeasurable
    hGt.aestronglyMeasurable, map_matrixQuotientMap_restrict']
  exact (measurePreserving_matrixUncurry F k m).integral_comp
    (matrixUncurry F k m).toHomeomorph.measurableEmbedding (fun t => G (torusLift t))

/-- **Unfolding rectangle integrals into torus integrals**: if the translates of `f` by the
rational matrices sum to the periodic continuous function `G` (in uncurried coordinates), then
`∫ f d(rectangleMeasure) = T_X G(X)`. -/
theorem integral_rectangleMeasure_eq_torusIntegral (k m : ℕ)
    (f : Matrix (Fin k) (Fin m) (Adeles F) → ℂ) (hf : Integrable f (rectangleMeasure F k m))
    (G : (Fin k × Fin m → Adeles F) → ℂ) (hG : IsPeriodic G) (hGc : Continuous G)
    (hfG : ∀ v, HasSum (fun c : rectLattice F k m => f (c + v)) (G (fun p => v p.1 p.2))) :
    ∫ v, f v ∂rectangleMeasure F k m =
      Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin k × Fin m) G := by
  have hfd := isAddFundamentalDomain_rectDomain F k m (rectangleMeasure F k m)
  have h1 : ∫ v, f v ∂rectangleMeasure F k m =
      ∑' c : rectLattice F k m, ∫ v in rectDomain F k m, f (c + v) ∂rectangleMeasure F k m := by
    rw [hfd.integral_eq_tsum' f hf]
    exact ((Equiv.neg (rectLattice F k m)).tsum_eq
      (fun c : rectLattice F k m => ∫ v in rectDomain F k m, f (c + v) ∂rectangleMeasure F k m))
  have hmeas : ∀ c : rectLattice F k m, AEStronglyMeasurable (fun v => f (c + v))
      ((rectangleMeasure F k m).restrict (rectDomain F k m)) := fun c =>
    ((hf.aestronglyMeasurable.comp_measurePreserving
      (measurePreserving_add_left (rectangleMeasure F k m)
        (c : Matrix (Fin k) (Fin m) (Adeles F))))).restrict
  have hlin : ∑' c : rectLattice F k m,
      ∫⁻ v in rectDomain F k m, ‖f (c + v)‖ₑ ∂rectangleMeasure F k m ≠ ⊤ := by
    have := hfd.lintegral_eq_tsum'' (fun v => ‖f v‖ₑ)
    simp only [AddSubgroup.vadd_def, vadd_eq_add] at this
    rw [← this]
    exact hf.hasFiniteIntegral.ne
  rw [h1, ← integral_tsum hmeas hlin, ← setIntegral_rectDomain_eq_torusIntegral F k m G hG hGc]
  refine setIntegral_congr_fun (measurableSet_rectDomain F k m) fun v _ => ?_
  exact (hfG v).tsum_eq

/-- Integrability from a uniform bound on the absolute periodization. -/
theorem integrable_of_tsum_norm_le (k m : ℕ) (f : Matrix (Fin k) (Fin m) (Adeles F) → ℂ)
    (hfc : Continuous f) {C : ℝ}
    (hs : ∀ v, Summable fun c : rectLattice F k m => ‖f (c + v)‖)
    (hC : ∀ v, ∑' c : rectLattice F k m, ‖f (c + v)‖ ≤ C) :
    Integrable f (rectangleMeasure F k m) := by
  refine ⟨hfc.aestronglyMeasurable, ?_⟩
  have hfd := isAddFundamentalDomain_rectDomain F k m (rectangleMeasure F k m)
  unfold HasFiniteIntegral
  rw [hfd.lintegral_eq_tsum'' (fun v => ‖f v‖ₑ)]
  simp only [AddSubgroup.vadd_def, vadd_eq_add]
  rw [← lintegral_tsum (fun c : rectLattice F k m =>
    (show Continuous fun v => f ((c : Matrix (Fin k) (Fin m) (Adeles F)) + v) from
      hfc.comp (continuous_const.add continuous_id)).enorm.aemeasurable)]
  refine lt_of_le_of_lt (setLIntegral_mono (g := fun _ => ENNReal.ofReal C) measurable_const
    fun v _ => ?_) ?_
  · simp only [← ofReal_norm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun c => norm_nonneg _) (hs v)]
    exact ENNReal.ofReal_le_ofReal (hC v)
  · rw [setLIntegral_const, rectangleMeasure_rectDomain, mul_one]
    exact ENNReal.ofReal_lt_top

end Torus

end Langlands.Global.RankinSelbergGlobal.Unfolding
