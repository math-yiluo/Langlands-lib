import Langlands.Automorphic.OperatorDeterminantSlicePairing

/-! # Support and covering-set estimates for the determinant-band measure -/

noncomputable section
universe uF uH
set_option autoImplicit false

open MeasureTheory Set Topology
open scoped ENNReal NNReal Pointwise

namespace Langlands.Global.LeftCosetSpace

variable {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
  (Γ : Subgroup H) (hΓ : IsDiscrete (Γ : Set H))
  (ν : Measure H) [ν.IsMulLeftInvariant]

/-- A full-support invariant measure gives full support on the discrete quotient. -/
theorem isOpenPosMeasure_discreteQuotientMeasure [ν.IsOpenPosMeasure]
    [OpensMeasurableSpace (Langlands.Global.LeftCosetSpace Γ)] :
    (discreteQuotientMeasure Γ hΓ ν).IsOpenPosMeasure := by
  let := countable_of_isDiscrete Γ hΓ
  constructor
  intro U hU hUne hzero
  have hinv (γ : Γ) : γ • (mk Γ ⁻¹' U) = mk Γ ⁻¹' U := by
    ext x
    simp only [mem_smul_set_iff_inv_smul_mem, mem_preimage]
    exact (congrArg (fun q => q ∈ U) (mk_subgroup_mul Γ γ⁻¹ x)).to_iff
  have hprezero : ν (mk Γ ⁻¹' U) = 0 := by
    apply (isFundamentalDomain Γ hΓ ν).measure_zero_of_invariant _ hinv
    exact (quotientMeasure_apply Γ ν (fundamentalDomain Γ hΓ) hU.measurableSet).symm.trans hzero
  have hpreopen := hU.preimage (continuous_mk Γ)
  have hprene : (mk Γ ⁻¹' U).Nonempty := by
    obtain ⟨q, hq⟩ := hUne
    obtain ⟨x, rfl⟩ := mk_surjective Γ q
    exact ⟨x, hq⟩
  exact hpreopen.measure_ne_zero ν hprene hprezero

/-- A measurable set meeting every orbit over `A` bounds its quotient integral. -/
theorem lintegral_restrict_discreteQuotientMeasure_le
    (A : Set (Langlands.Global.LeftCosetSpace Γ)) (hA : MeasurableSet A)
    (t : Set H) (ht : MeasurableSet t)
    (hcover : ∀ x : H, mk Γ x ∈ A → ∃ γ : Γ, (γ : H) * x ∈ t)
    (f : Langlands.Global.LeftCosetSpace Γ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ q in A, f q ∂discreteQuotientMeasure Γ hΓ ν ≤
      ∫⁻ x in t, f (mk Γ x) ∂ν := by
  classical
  let := countable_of_isDiscrete Γ hΓ
  let s := fundamentalDomain Γ hΓ
  let k : H → ℝ≥0∞ := t.indicator (fun x => f (mk Γ x))
  have hk : Measurable k := (hf.comp (measurable_mk Γ)).indicator ht
  have hbound (x : H) : A.indicator f (mk Γ x) ≤ ∑' γ : Γ, k ((γ : H) * x) := by
    by_cases hx : mk Γ x ∈ A
    · obtain ⟨γ, hγ⟩ := hcover x hx
      calc
        A.indicator f (mk Γ x) = f (mk Γ x) := indicator_of_mem hx f
        _ = k ((γ : H) * x) := by
          dsimp only [k]
          rw [indicator_of_mem hγ, mk_subgroup_mul]
        _ ≤ _ := ENNReal.le_tsum (f := fun γ : Γ => k ((γ : H) * x)) γ
    · rw [indicator_of_notMem hx]
      exact zero_le
  calc
    _ = ∫⁻ q, A.indicator f q ∂discreteQuotientMeasure Γ hΓ ν :=
      (lintegral_indicator hA f).symm
    _ = ∫⁻ x in s, A.indicator f (mk Γ x) ∂ν := by
      exact lintegral_map (hf.indicator hA) (measurable_mk Γ)
    _ ≤ ∫⁻ x in s, ∑' γ : Γ, k ((γ : H) * x) ∂ν := lintegral_mono hbound
    _ = ∑' γ : Γ, ∫⁻ x in s, k ((γ : H) * x) ∂ν := by
      rw [lintegral_tsum]
      intro γ
      exact (hk.comp (measurable_const.mul measurable_id)).aemeasurable
    _ = ∫⁻ x, k x ∂ν := ((isFundamentalDomain Γ hΓ ν).lintegral_eq_tsum'' k).symm
    _ = _ := lintegral_indicator ht (fun x => f (mk Γ x))

end Langlands.Global.LeftCosetSpace

namespace Langlands.Automorphic.OperatorDeterminantSlice

open CategoryTheory _root_.AlgebraicGeometry Langlands.Global ContinuousRationalFunctions
open scoped CategoryTheory.MonObj

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)
local instance measureIsAffine : IsAffine (matrixGroupScheme F n).X.left :=
  Langlands.GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)
local instance measureSmooth : Smooth (matrixGroupScheme F n).X.hom :=
  Langlands.GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

/-- The already constructed rational quotient Haar measure in these coordinates. -/
def quotientHaarMeasure : Measure (Quotient F n) :=
  AdelicGroupPoints.rationalQuotientHaarMeasure F (matrixGroupScheme F n)

instance quotientHaarMeasure_isOpenPosMeasure : (quotientHaarMeasure F n).IsOpenPosMeasure :=
  LeftCosetSpace.isOpenPosMeasure_discreteQuotientMeasure
    (AdelicGroupPoints.rationalSubgroup F (matrixGroupScheme F n))
    (AdelicGroupPoints.isDiscrete_rationalSubgroup F (matrixGroupScheme F n)) Measure.haar

variable [MeasurableSpace (AdelicGL F n)] [BorelSpace (AdelicGL F n)]

/-- The same actual Haar measure in the original adelic matrix coordinates. -/
def matrixHaarMeasure : Measure (AdelicGL F n) :=
  Measure.map (GeneralLinearGroupPoints.adelicHomeomorph F n) Measure.haar

instance matrixHaarMeasure_isHaarMeasure : (matrixHaarMeasure F n).IsHaarMeasure :=
  (GeneralLinearGroupPoints.adelicHomeomorph F n).isHaarMeasure_map Measure.haar

variable (S : OperatorRealization F n)
local instance : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup S.Space := Submodule.addCommGroup _

/-- A matrix covering set controls the original quotient function's band integral. -/
theorem lintegral_band_le_cover
    (t : Set (AdelicGL F n)) (ht : MeasurableSet t)
    (hcover : ∀ x : AdelicGL F n,
      1 ≤ ((AdelicBlockDeterminantCharacter.determinantNorm F n x : ℝ≥0) : ℝ) ∧
        ((AdelicBlockDeterminantCharacter.determinantNorm F n x : ℝ≥0) : ℝ) ≤ 2 →
      ∃ γ : RationalGL F n, AdelicGL.rational F n γ * x ∈ t)
    (f : S.Space) :
    ∫⁻ q in band F n, ‖toQuotient F n S f q‖ₑ ^ 2 ∂quotientHaarMeasure F n ≤
      ∫⁻ x in t, ‖evaluate F n (S.toContinuous f) x‖ₑ ^ 2 ∂matrixHaarMeasure F n := by
  let e := GeneralLinearGroupPoints.adelicHomeomorph F n
  let Γ := AdelicGroupPoints.rationalSubgroup F (matrixGroupScheme F n)
  have hcov : ∀ x : AdelicGroupPoints F (matrixGroupScheme F n),
      LeftCosetSpace.mk Γ x ∈ band F n → ∃ γ : Γ, (γ : _) * x ∈ e ⁻¹' t := by
    intro x hx
    change 1 < (groupDeterminantNorm F n x : ℝ≥0) ∧
      (groupDeterminantNorm F n x : ℝ≥0) < 2 at hx
    obtain ⟨γ, hγ⟩ := hcover (e x) ⟨by exact_mod_cast hx.1.le, by exact_mod_cast hx.2.le⟩
    let r := (GeneralLinearGroupPoints.rationalEquiv F n).symm γ
    refine ⟨⟨AdelicGroupPoints.rational F (matrixGroupScheme F n) r, ⟨r, rfl⟩⟩, ?_⟩
    change e (AdelicGroupPoints.rational F (matrixGroupScheme F n) r * x) ∈ t
    simpa only [e, r, map_mul, GeneralLinearGroupPoints.adelicHomeomorph_rational,
      MulEquiv.apply_symm_apply] using hγ
  have hle := LeftCosetSpace.lintegral_restrict_discreteQuotientMeasure_le Γ
    (AdelicGroupPoints.isDiscrete_rationalSubgroup F (matrixGroupScheme F n))
    Measure.haar (band F n) (measurableSet_band F n) (e ⁻¹' t)
    (ht.preimage e.continuous.measurable) hcov
    (fun q => ‖toQuotient F n S f q‖ₑ ^ 2)
    ((toQuotient F n S f).continuous.measurable.enorm.pow_const 2)
  apply hle.trans_eq
  rw [← lintegral_indicator ht _, matrixHaarMeasure,
    lintegral_map (g := fun x => e x) (by
      exact ((continuous_evaluate F n (S.toContinuous f)).measurable.enorm.pow_const 2).indicator ht)
      (show Measurable (fun x => e x) from e.continuous.measurable),
    ← lintegral_indicator
      (ht.preimage (show Measurable (fun x => e x) from e.continuous.measurable)) _]
  rfl

/-- Square integrability on one rational covering set gives band `L²` membership. -/
theorem memLp_band_of_cover
    (t : Set (AdelicGL F n)) (ht : MeasurableSet t)
    (hcover : ∀ x : AdelicGL F n,
      1 ≤ ((AdelicBlockDeterminantCharacter.determinantNorm F n x : ℝ≥0) : ℝ) ∧
        ((AdelicBlockDeterminantCharacter.determinantNorm F n x : ℝ≥0) : ℝ) ≤ 2 →
      ∃ γ : RationalGL F n, AdelicGL.rational F n γ * x ∈ t)
    (f : S.Space)
    (hf : ∫⁻ x in t, ‖evaluate F n (S.toContinuous f) x‖ₑ ^ 2
      ∂matrixHaarMeasure F n < ∞) :
    MemLp (toQuotient F n S f) 2 ((quotientHaarMeasure F n).restrict (band F n)) := by
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)
    (toQuotient F n S f).continuous.aestronglyMeasurable).mpr
  simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
    (lintegral_band_le_cover F n S t ht hcover f).trans_lt hf

end Langlands.Automorphic.OperatorDeterminantSlice
