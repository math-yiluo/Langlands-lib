import Langlands.Automorphic.OperatorDeterminantSliceGeometry
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # The determinant-band form on the original operator realization -/

noncomputable section
universe uF
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MeasureTheory Filter
open scoped CategoryTheory.MonObj InnerProductSpace NNReal

namespace Langlands.Automorphic.OperatorDeterminantSlice

open Langlands.Global ContinuousRationalFunctions NumberField

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)

local instance pairingIsAffine : IsAffine (matrixGroupScheme F n).X.left :=
  Langlands.GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)
local instance pairingSmooth : Smooth (matrixGroupScheme F n).X.hom :=
  Langlands.GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)
local instance : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

/-- A coset represented in the original matrix model. -/
def point (x : AdelicGL F n) : Quotient F n :=
  LeftCosetSpace.mk (AdelicGroupPoints.rationalSubgroup F (matrixGroupScheme F n))
    ((GeneralLinearGroupPoints.adelicHomeomorph F n).symm x)

theorem point_surjective : Function.Surjective (point F n) := by
  intro q
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective
    (AdelicGroupPoints.rationalSubgroup F (matrixGroupScheme F n)) q
  exact ⟨GeneralLinearGroupPoints.adelicHomeomorph F n x, by simp [point]⟩

/-- Positive right translation, indexed by the original matrix group. -/
def translate (g : AdelicGL F n) : Quotient F n ≃ₜ Quotient F n :=
  LeftCosetSpace.rightTranslateHomeomorph
    (AdelicGroupPoints.rationalSubgroup F (matrixGroupScheme F n))
    ((GeneralLinearGroupPoints.adelicHomeomorph F n).symm g)

@[simp]
theorem translate_point (g x : AdelicGL F n) :
    translate F n g (point F n x) = point F n (x * g) := by
  change LeftCosetSpace.mk _
    ((GeneralLinearGroupPoints.adelicHomeomorph F n).symm x *
      (GeneralLinearGroupPoints.adelicHomeomorph F n).symm g) = _
  rw [point, map_mul]

@[simp]
theorem quotientDeterminantNorm_point (x : AdelicGL F n) :
    quotientDeterminantNorm F n (point F n x) =
      AdelicBlockDeterminantCharacter.determinantNorm F n x := by
  change AdelicBlockDeterminantCharacter.determinantNorm F n
    (GeneralLinearGroupPoints.adelicHomeomorph F n
      ((GeneralLinearGroupPoints.adelicHomeomorph F n).symm x)) = _
  rw [ContinuousMulEquiv.apply_symm_apply]

variable (S : OperatorRealization F n)
local instance : AddCommGroup S.Space := Submodule.addCommGroup _

@[simp]
theorem toQuotient_point (f : S.Space) (x : AdelicGL F n) :
    toQuotient F n S f (point F n x) = evaluate F n (S.toContinuous f) x := by
  change evaluate F n (S.toContinuous f)
    (GeneralLinearGroupPoints.adelicHomeomorph F n
      ((GeneralLinearGroupPoints.adelicHomeomorph F n).symm x)) = _
  rw [ContinuousMulEquiv.apply_symm_apply]

set_option maxHeartbeats 500000 in
/-- The original finite action is the same positive right translation. -/
theorem toQuotient_finite (d : FiniteAdelicGL F n) (f : S.Space) (q : Quotient F n) :
    toQuotient F n S (S.finiteRepresentation d f) q =
      toQuotient F n S f (translate F n (AdelicGL.ofFinite F n d) q) := by
  obtain ⟨x, rfl⟩ := point_surjective F n q
  simp only [translate_point, toQuotient_point, OperatorRealization.evaluate_finiteRepresentation]

/-- The common central character is retained on the quotient function. -/
theorem toQuotient_central (χ : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (hS : S.HasCentralCharacter χ) (z : Ideles F) (f : S.Space)
    (g : AdelicGL F n) (q : Quotient F n) :
    toQuotient F n S f (translate F n (AdelicGL.scalar F n z * g) q) =
      (centralIdeleCharacter F χ z : ℂ) *
        toQuotient F n S f (translate F n g q) := by
  obtain ⟨x, rfl⟩ := point_surjective F n q
  simp only [translate_point, toQuotient_point]
  rw [← mul_assoc, ← (AdelicGL.scalar_commute F n z x).eq, mul_assoc]
  exact S.centralCharacter_evaluate χ hS f z (x * g)

/-- The original continuous function as an `L²` vector on the open band. -/
def toL2 (measure : Measure (Quotient F n))
    (hL2 : ∀ f : S.Space, MemLp (toQuotient F n S f) 2 (measure.restrict (band F n))) :
    S.Space →ₗ[ℂ] Lp ℂ 2 (measure.restrict (band F n)) where
  toFun f := (hL2 f).toLp (toQuotient F n S f)
  map_add' f g := by
    simpa only [map_add, ContinuousMap.coe_add] using (hL2 f).toLp_add (hL2 g)
  map_smul' c f := by
    simpa only [map_smul, ContinuousMap.coe_smul, RingHom.id_apply] using (hL2 f).toLp_const_smul c

@[simp]
theorem inner_toL2 (measure : Measure (Quotient F n))
    (hL2 : ∀ f : S.Space, MemLp (toQuotient F n S f) 2 (measure.restrict (band F n)))
    (f g : S.Space) :
    inner ℂ (toL2 F n S measure hL2 f) (toL2 F n S measure hL2 g) =
      ∫ q, inner ℂ (toQuotient F n S f q) (toQuotient F n S g q)
        ∂measure.restrict (band F n) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hL2 f).coeFn_toLp, (hL2 g).coeFn_toLp] with q hf hg
  exact congrArg₂ (inner ℂ) hf hg

/-- Continuity and the central character make equality on the band faithful. -/
theorem toL2_injective (hn : n ≠ 0) (measure : Measure (Quotient F n))
    [measure.IsOpenPosMeasure]
    (χ : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) (hS : S.HasCentralCharacter χ)
    (hL2 : ∀ f : S.Space, MemLp (toQuotient F n S f) 2 (measure.restrict (band F n))) :
    Function.Injective (toL2 F n S measure hL2) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro f hf
  have hae : toQuotient F n S f =ᵐ[measure.restrict (band F n)] 0 := by
    have hzero : (hL2 f).toLp (toQuotient F n S f) =
        (MemLp.zero : MemLp (0 : Quotient F n → ℂ) 2
          (measure.restrict (band F n))).toLp 0 := by
      simpa only [toL2, LinearMap.coe_mk, AddHom.coe_mk, MemLp.toLp_zero] using hf
    exact (MemLp.toLp_eq_toLp_iff _ _).mp hzero
  have hband := Measure.eqOn_open_of_ae_eq hae (isOpen_band F n)
    (toQuotient F n S f).continuous.continuousOn continuousOn_const
  apply (toQuotient F n S).map_eq_zero_iff (toQuotient_injective F n S) |>.mp
  apply ContinuousMap.ext
  intro q
  obtain ⟨x, rfl⟩ := point_surjective F n q
  let t : ℝ≥0ˣ := Units.mk0 (3 / 2 : ℝ≥0) (by norm_num)
  obtain ⟨z, hz⟩ := exists_scalar_determinantNorm F n hn
    (t * (AdelicBlockDeterminantCharacter.determinantNorm F n x)⁻¹)
  have hzband : point F n (AdelicGL.scalar F n z * x) ∈ band F n := by
    change 1 < (quotientDeterminantNorm F n _ : ℝ≥0) ∧
      (quotientDeterminantNorm F n _ : ℝ≥0) < 2
    rw [quotientDeterminantNorm_point, map_mul, hz, inv_mul_cancel_right]
    norm_num [t]
  have heq := hband hzband
  simp only [toQuotient_point, Pi.zero_apply] at heq
  rw [S.centralCharacter_evaluate χ hS f z x] at heq
  simpa only [toQuotient_point, ContinuousMap.zero_apply] using
    (mul_eq_zero.mp heq).resolve_left (Units.ne_zero _)

/-- Transport the norm-one restriction lemma to the original matrix group. -/
theorem measurePreserving_translate_band (measure : Measure (Quotient F n))
    (g : AdelicGL F n)
    (hg : AdelicBlockDeterminantCharacter.determinantNorm F n g = 1)
    (hmeasure : MeasurePreserving (translate F n g) measure measure) :
    MeasurePreserving (translate F n g)
      (measure.restrict (band F n)) (measure.restrict (band F n)) := by
  apply measurePreserving_band F n measure
    ((GeneralLinearGroupPoints.adelicHomeomorph F n).symm g) _ hmeasure
  change AdelicBlockDeterminantCharacter.determinantNorm F n
    (GeneralLinearGroupPoints.adelicHomeomorph F n
      ((GeneralLinearGroupPoints.adelicHomeomorph F n).symm g)) = 1
  rw [ContinuousMulEquiv.apply_symm_apply]
  exact hg

/-- A common phase of norm one cancels from the pointwise Hermitian product. -/
theorem inner_phase (c a b : ℂ) (hc : ‖c‖ = 1) :
    inner ℂ (c * a) (c * b) = inner ℂ a b := by
  change inner ℂ (c • a) (c • b) = _
  rw [inner_smul_left, inner_smul_right, ← mul_assoc]
  have hc' : starRingEnd ℂ c * c = 1 := by
    simpa only [hc, one_pow, Complex.ofReal_one] using Complex.conj_mul' c
  rw [hc', one_mul]

set_option maxHeartbeats 1500000 in
/-- Normalized right translation proves invariance for the original finite action. -/
theorem inner_toL2_finite (hn : n ≠ 0) (measure : Measure (Quotient F n))
    (χ : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (hχ : ∀ x, ‖(χ x : ℂ)‖ = 1) (hS : S.HasCentralCharacter χ)
    (hL2 : ∀ f : S.Space, MemLp (toQuotient F n S f) 2 (measure.restrict (band F n)))
    (hmeasure : ∀ g : AdelicGL F n,
      AdelicBlockDeterminantCharacter.determinantNorm F n g = 1 →
        MeasurePreserving (translate F n g) measure measure)
    (d : FiniteAdelicGL F n) (f g : S.Space) :
    inner ℂ (toL2 F n S measure hL2 (S.finiteRepresentation d f))
      (toL2 F n S measure hL2 (S.finiteRepresentation d g)) =
        inner ℂ (toL2 F n S measure hL2 f) (toL2 F n S measure hL2 g) := by
  obtain ⟨z, hz⟩ := exists_normalized_rightTranslate F n hn (AdelicGL.ofFinite F n d)
  let a := AdelicGL.scalar F n z * AdelicGL.ofFinite F n d
  have ha := measurePreserving_translate_band F n measure a hz (hmeasure a hz)
  rw [inner_toL2, inner_toL2]
  calc
    _ = ∫ q, inner ℂ (toQuotient F n S f (translate F n a q))
        (toQuotient F n S g (translate F n a q)) ∂measure.restrict (band F n) := by
      apply integral_congr_ae
      filter_upwards [] with q
      dsimp only [a]
      rw [toQuotient_finite, toQuotient_finite,
        toQuotient_central F n S χ hS, toQuotient_central F n S χ hS]
      exact (inner_phase _ _ _ (hχ _)).symm
    _ = _ := ha.integral_comp
      (translate F n a).toMeasurableEquiv.measurableEmbedding
      (fun q => inner ℂ (toQuotient F n S f q) (toQuotient F n S g q))

set_option maxHeartbeats 1500000 in
/-- Pull the band integral back to the unchanged finite representation. -/
def finiteInvariantPositiveForm (hn : n ≠ 0) (measure : Measure (Quotient F n))
    [measure.IsOpenPosMeasure]
    (χ : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (hχ : ∀ x, ‖(χ x : ℂ)‖ = 1) (hS : S.HasCentralCharacter χ)
    (hL2 : ∀ f : S.Space, MemLp (toQuotient F n S f) 2 (measure.restrict (band F n)))
    (hmeasure : ∀ g : AdelicGL F n,
      AdelicBlockDeterminantCharacter.determinantNorm F n g = 1 →
        MeasurePreserving (translate F n g) measure measure) :
    Langlands.InvariantPositiveForm S.finiteRepresentation where
  inner f g := inner ℂ (toL2 F n S measure hL2 f) (toL2 F n S measure hL2 g)
  conj_inner_symm f g := inner_conj_symm _ _
  re_inner_nonneg f := inner_self_nonneg
  add_left f g h := by rw [map_add, inner_add_left]
  smul_left f g c := by rw [map_smul, inner_smul_left]
  definite f hf := toL2_injective F n S hn measure χ hS hL2 <| by
    simpa only [map_zero] using (inner_self_eq_zero.mp hf)
  invariant d f g := inner_toL2_finite F n S hn measure χ hχ hS hL2 hmeasure d f g

end Langlands.Automorphic.OperatorDeterminantSlice
