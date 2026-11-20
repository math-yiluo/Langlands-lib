import Langlands.Automorphic.OperatorDeterminantSliceMeasure
import Langlands.Global.LeftCosetLocalMeasure

/-! # Local Haar integration within the actual determinant band -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000

open scoped CategoryTheory.MonObj ENNReal NNReal

namespace Langlands.Automorphic.OperatorDeterminantSlice

open Langlands.Global ContinuousRationalFunctions MeasureTheory Set CategoryTheory
  _root_.AlgebraicGeometry

universe u

attribute [local instance] measureIsAffine measureSmooth

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

/-- Every point in the band has an open matrix neighborhood on which the
actual quotient projection is injective and remains in the band. -/
theorem exists_open_injective_bandPatch (g : AdelicGL F n) (hg : point F n g ∈ band F n) :
    ∃ t : Set (AdelicGL F n), IsOpen t ∧ g ∈ t ∧ t.InjOn (point F n) ∧
      MapsTo (point F n) t (band F n) := by
  let e := GeneralLinearGroupPoints.adelicHomeomorph F n
  let Γ := AdelicGroupPoints.rationalSubgroup F (matrixGroupScheme F n)
  have hΓ := AdelicGroupPoints.isDiscrete_rationalSubgroup F (matrixGroupScheme F n)
  have hlocal := (LeftCosetSpace.isQuotientCoveringMap_mk Γ hΓ).isCoveringMap.isLocalHomeomorph.isLocallyInjective
  obtain ⟨U, hUo, hgU, hU⟩ := hlocal (e.symm g)
  have hp : Continuous (point F n) := (LeftCosetSpace.continuous_mk Γ).comp e.symm.continuous
  let t := e.symm ⁻¹' U ∩ point F n ⁻¹' band F n
  refine ⟨t, (hUo.preimage e.symm.continuous).inter ((isOpen_band F n).preimage hp),
    ⟨hgU, hg⟩, ?_, fun _ hx => hx.2⟩
  intro x hx y hy hxy
  exact e.symm.injective (hU hx.1 hy.1 hxy)

local instance patchRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance patchContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance patchFiniteSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance patchFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance patchStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

variable (S : OperatorRealization F n)
local instance patchSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

variable [MeasurableSpace (AdelicGL F n)] [BorelSpace (AdelicGL F n)]

/-- The ambient squared norm on an injective matrix patch lying in the
band is bounded by the actual quotient integral for that band. -/
theorem lintegral_bandPatch_le
    (t : Set (AdelicGL F n)) (ht : MeasurableSet t) (hinj : t.InjOn (point F n))
    (hband : MapsTo (point F n) t (band F n)) (v : S.Space) :
    ∫⁻ x in t, ‖evaluate F n (S.toContinuous v) x‖ₑ ^ 2 ∂matrixHaarMeasure F n ≤
      ∫⁻ q in band F n, ‖toQuotient F n S v q‖ₑ ^ 2 ∂quotientHaarMeasure F n := by
  let e := GeneralLinearGroupPoints.adelicHomeomorph F n
  let Γ := AdelicGroupPoints.rationalSubgroup F (matrixGroupScheme F n)
  let u := e ⁻¹' t
  have hu : MeasurableSet u := ht.preimage e.continuous.measurable
  have hp (x : AdelicGroupPoints F (matrixGroupScheme F n)) :
      point F n (e x) = LeftCosetSpace.mk Γ x :=
    congrArg (LeftCosetSpace.mk Γ) (e.symm_apply_apply x)
  have hui : u.InjOn (LeftCosetSpace.mk Γ) := by
    intro x hx y hy hxy
    apply e.injective
    apply hinj hx hy
    exact (hp x).trans (hxy.trans (hp y).symm)
  have hmap : MapsTo (LeftCosetSpace.mk Γ) u (band F n) :=
    fun x hx => (hp x) ▸ hband hx
  have hle := LeftCosetSpace.lintegral_restrict_le_discreteQuotientMeasure Γ
    (AdelicGroupPoints.isDiscrete_rationalSubgroup F (matrixGroupScheme F n))
    Measure.haar u hu hui (band F n) (measurableSet_band F n) hmap
    (fun q => ‖toQuotient F n S v q‖ₑ ^ 2)
    ((toQuotient F n S v).continuous.measurable.enorm.pow_const 2)
  let p : AdelicGL F n → ℝ≥0∞ := fun g => ‖evaluate F n (S.toContinuous v) g‖ₑ ^ 2
  have hf : Measurable p := (continuous_evaluate F n (S.toContinuous v)).measurable.enorm.pow_const 2
  let k : AdelicGroupPoints F (matrixGroupScheme F n) → ℝ≥0∞ :=
    fun x => ‖toQuotient F n S v (LeftCosetSpace.mk Γ x)‖ₑ ^ 2
  calc
    _ = ∫⁻ x, t.indicator p (e x) ∂Measure.haar := by
      change ∫⁻ x in t, p x ∂matrixHaarMeasure F n = _
      rw [← lintegral_indicator ht, matrixHaarMeasure]
      exact lintegral_map (g := fun x => e x) (hf.indicator ht)
        (show Measurable (fun x => e x) from e.continuous.measurable)
    _ = ∫⁻ x in u, ‖toQuotient F n S v (LeftCosetSpace.mk Γ x)‖ₑ ^ 2
        ∂Measure.haar := by
      rw [← lintegral_indicator hu]
      apply lintegral_congr
      intro x
      change t.indicator p (e x) = u.indicator k x
      by_cases hx : x ∈ u
      · have he : e x ∈ t := hx
        have hpv := congrArg (fun q : Quotient F n => ‖toQuotient F n S v q‖ₑ ^ (2 : ℕ)) (hp x)
        have hkv : p (e x) = k x :=
          (congrArg (fun z : ℂ => ‖z‖ₑ ^ (2 : ℕ)) (toQuotient_point F n S v (e x)).symm).trans hpv
        exact (indicator_of_mem he p).trans (hkv.trans (indicator_of_mem hx k).symm)
      · have he : e x ∉ t := hx
        exact (indicator_of_notMem he p).trans (indicator_of_notMem hx k).symm
    _ ≤ _ := hle

private theorem eLpNorm_two_eq {M : Type*} [MeasurableSpace M] {m : Measure M}
    {f : M → ℂ} (hf : AEStronglyMeasurable f m) :
    eLpNorm f 2 m = (∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ) ∂m) ^ (1 / 2 : ℝ) := by
  simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
    eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num) (by norm_num) hf

/-- The `L²` seminorm of a realized vector on an injective patch is
controlled by its actual determinant-band `L²` norm. -/
theorem eLpNorm_bandPatch_le
    (hL2 : ∀ v : S.Space,
      MemLp (toQuotient F n S v) 2 ((quotientHaarMeasure F n).restrict (band F n)))
    (t : Set (AdelicGL F n)) (ht : MeasurableSet t) (hinj : t.InjOn (point F n))
    (hband : MapsTo (point F n) t (band F n)) (v : S.Space) :
    eLpNorm (evaluate F n (S.toContinuous v)) 2 ((matrixHaarMeasure F n).restrict t) ≤
      ‖toL2 F n S (quotientHaarMeasure F n) hL2 v‖ₑ := by
  let m := (matrixHaarMeasure F n).restrict t
  let ν := (quotientHaarMeasure F n).restrict (band F n)
  let f := evaluate F n (S.toContinuous v)
  let q : Quotient F n → ℂ := toQuotient F n S v
  have hf : AEStronglyMeasurable f m :=
    (continuous_evaluate F n (S.toContinuous v)).aestronglyMeasurable
  have hq : MemLp q 2 ν := hL2 v
  change eLpNorm f 2 m ≤ ‖hq.toLp q‖ₑ
  calc
    eLpNorm f 2 m = _ := eLpNorm_two_eq hf
    _ ≤ (∫⁻ x, ‖q x‖ₑ ^ (2 : ℕ) ∂ν) ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow (lintegral_bandPatch_le F n S t ht hinj hband v) (by positivity)
    _ = eLpNorm q 2 ν := (eLpNorm_two_eq hq.aestronglyMeasurable).symm
    _ = ‖hq.toLp q‖ₑ := (Lp.enorm_toLp hq).symm

end Langlands.Automorphic.OperatorDeterminantSlice
