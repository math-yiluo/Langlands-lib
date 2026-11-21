import Langlands.Automorphic.RealizationSummandBandMeasure
import Langlands.Automorphic.GeneralLinearParabolicCuspidalEquivalence
import Langlands.Automorphic.GroupSchemeFullAEL2Continuous
import Langlands.Automorphic.CuspidalBandOrbitClosure

/-! # Classes of positive-central invariant cuspidal forms

The determinant-band comparison gives an injective class map into the full AE cuspidal
`L²` space. Pairing against a band pullback transfers the actual adelic orbit coefficients
from the band to the positive-central quotient. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory NumberField
open scoped CategoryTheory.MonObj ComplexInnerProductSpace

set_option autoImplicit false

namespace Langlands.Automorphic.RealizationSummand

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus
open Langlands.GroupScheme GroupSchemeFunctions

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  (r : ℕ) (T : CommGroupScheme (Spec (CommRingCat.of F)))
  (i : T.toGrp ⟶ GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))

local notation "n" => (r + 1)
local notation "GLG" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)
local notation "Q" => PositiveRationalQuotient F GLG T i
local notation "μQ" => positiveRationalQuotientHaarMeasure F GLG T i
local notation "aGL" => GeneralLinearGroupPoints.adelicHomeomorph F n
local notation "ΓQ" => positiveRationalSubgroup F GLG T i

local instance classMapIsAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance classMapSmooth : Smooth (GLG).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

variable (R : CuspidalOperatorRealization F r)

local instance : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup R.Space := Submodule.addCommGroup _

/-- The descent hypothesis of the target statement. -/
abbrev HasPositiveDescent : Prop :=
  ∀ f : R.Space, ∃ h : C(Q, ℂ),
    continuousGeneralLinearEquiv F n (positiveQuotientContinuousPullback F GLG T i h) =
      R.realization.toContinuous f

variable (hdesc : HasPositiveDescent F r T i R)

set_option maxHeartbeats 800000 in
/-- The continuous descended functions are unique, and therefore depend linearly on the
source vector. -/
def descended : R.Space →ₗ[ℂ] C(Q, ℂ) where
  toFun f := Classical.choose (hdesc f)
  map_add' f g := by
    apply (positiveQuotientContinuousPullback_injective F GLG T i)
    apply (continuousGeneralLinearEquiv F n).injective
    rw [(hdesc (f + g)).choose_spec]
    simp only [map_add, (hdesc f).choose_spec, (hdesc g).choose_spec]
  map_smul' z f := by
    apply (positiveQuotientContinuousPullback_injective F GLG T i)
    apply (continuousGeneralLinearEquiv F n).injective
    rw [(hdesc (z • f)).choose_spec]
    simp only [RingHom.id_apply, map_smul, (hdesc f).choose_spec]

local notation "hform" => descended F r T i R hdesc
local notation "pQ" => projection F n T i
local notation "μB" => CuspidalHilbertOrbitCoefficient.bandMeasure F r

/-- The representative pulls back to the original matrix-model function. -/
theorem descended_pullback (f : R.Space) :
    continuousGeneralLinearEquiv F n (positiveQuotientContinuousPullback F GLG T i (hform f)) =
      R.realization.toContinuous f :=
  (hdesc f).choose_spec

set_option maxHeartbeats 800000 in
theorem descended_injective : Function.Injective hform := by
  intro f g h
  apply R.realization.toContinuous_injective
  rw [← descended_pullback F r T i R hdesc f, h, descended_pullback]

set_option maxHeartbeats 800000 in
/-- On the principal quotient the representative is the original descended function. -/
theorem toQuotient_eq_descended (f : R.Space) (q : OperatorDeterminantSlice.Quotient F n) :
    OperatorDeterminantSlice.toQuotient F n R.realization f q = hform f (pQ q) := by
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective (rationalSubgroup F GLG) q
  change ((continuousGeneralLinearEquiv F n).symm (R.realization.toContinuous f)).val.val x =
    hform f (LeftCosetSpace.mk ΓQ x)
  rw [← descended_pullback F r T i R hdesc f, LinearEquiv.symm_apply_apply,
    positiveQuotientContinuousPullback_apply]

omit [CompactSpace (AdeleQuotient F)] in
/-- The principal projection intertwines the same right translations on the two quotients. -/
theorem projection_translate (a : AdelicGL F n) (q : OperatorDeterminantSlice.Quotient F n) :
    pQ (OperatorDeterminantSlice.translate F n a q) =
      LeftCosetSpace.rightTranslate ΓQ ((aGL).symm a) (pQ q) :=
  projection_rightTranslate F n T i ((aGL).symm a) q

set_option maxHeartbeats 800000 in
theorem memLp_descended_comp_projection (f : R.Space) :
    MemLp (hform f ∘ pQ) 2 μB := by
  have h : (fun q => OperatorDeterminantSlice.toQuotient F n R.realization f
      (OperatorDeterminantSlice.translate F n 1 q)) = hform f ∘ pQ := by
    funext q
    rw [OperatorDeterminantSlice.translate_one]
    exact toQuotient_eq_descended F r T i R hdesc f _
  rw [← h]
  exact OperatorDeterminantSlice.memLp_translate_of_cuspidal R.realization R.cuspidal 1 f

variable (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)

local notation "cB" => bandConstant F n T i hi I e hc

include hi e hc in
/-- The descended functions are square integrable on the positive-central quotient. -/
theorem memLp_descended (f : R.Space) : MemLp (hform f) 2 μQ := by
  let _ := positiveRationalQuotient_borelSpace F GLG T i hi I e hc
  exact memLp_of_comp_projection F n T i hi I e hc (Nat.succ_ne_zero r) _
    (hform f).continuous.aestronglyMeasurable (memLp_descended_comp_projection F r T i R hdesc f)

variable [hHaar : (Measure.haar : Measure (normOneSubgroup F
  (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))).IsMulRightInvariant]

include hdesc in
/-- Nontriviality of the source forces the band comparison constant to be finite. -/
theorem bandConstant_ne_top_of_descent : cB ≠ ⊤ := by
  obtain ⟨f, hf⟩ := exists_ne (0 : R.Space)
  apply bandConstant_ne_top F n T i hi I e hc (hform f)
  · intro h
    apply hf (descended_injective F r T i R hdesc (h.trans (map_zero _).symm))
  · exact memLp_descended_comp_projection F r T i R hdesc f

variable (hPD : ParabolicDynamicStatement.{u})

local notation "hG" => GroupScheme.isConnectedReductive_generalLinear F (Fin n)
local notation "S" => fullAEL2CuspidalSubmodule F GLG hPD hG T i hi I e hc
local notation "πc" => fullAEL2CuspidalBoundedRightAction F GLG hPD hG T i hi I e hc
local notation "hR" => haarQuotientMeasureRightInvariant F GLG T i hi I e hc
local notation "mDesc" => memLp_descended F r T i R hdesc hi I e hc

omit [(characterRestrict i).range.FiniteIndex] hHaar in
/-- All proper periods of the continuous quotient representative converge and vanish almost
 everywhere, by the matrix-to-parabolic cuspidality comparison. -/
theorem descended_aeCuspidal (f : R.Space) :
    (hform f : Q → ℂ) ∈ aeParabolicCuspidalFunctionSubmodule F GLG hPD hG T i := by
  apply mem_aeParabolicCuspidalFunctionSubmodule_of_continuous
  apply (mem_positiveParabolicCuspidalSubrepresentation F GLG T i hPD hG _ _).mpr
  apply (mem_normalizedGeneralLinearParabolicCuspidal_iff F n hPD hG _).mpr
  rw [descended_pullback]
  exact R.isCuspidal_vector f

/-- Send each realized vector to the class of its continuous quotient representative in the
unchanged full AE cuspidal carrier. -/
def classMap : R.Space →ₗ[ℂ] S where
  toFun f := ⟨(mDesc f).toLp (hform f), by
    let _ := positiveRationalQuotient_borelSpace F GLG T i hi I e hc
    change (((mDesc f).toLp (hform f) : Lp ℂ 2 μQ) : Q → ℂ) ∈
      aeParabolicCuspidalFunctionSubmodule F GLG hPD hG T i
    exact (mem_aeParabolicCuspidalFunctionSubmodule_congr F GLG hPD hG T i hi I e hc
      _ _ (Lp.stronglyMeasurable _) (hform f).continuous.stronglyMeasurable
      (mDesc f).coeFn_toLp).mpr (descended_aeCuspidal F r T i R hdesc hPD f)⟩
  map_add' f g := by
    apply Subtype.ext
    change (mDesc (f + g)).toLp _ = (mDesc f).toLp _ + (mDesc g).toLp _
    simpa only [map_add, ContinuousMap.coe_add] using (mDesc f).toLp_add (mDesc g)
  map_smul' z f := by
    apply Subtype.ext
    change (mDesc (z • f)).toLp _ = z • (mDesc f).toLp _
    simpa only [map_smul, ContinuousMap.coe_smul] using
      (mDesc f).toLp_const_smul z

local notation "Φ" => classMap F r T i R hdesc hi I e hc hPD

omit hHaar in
theorem coeFn_classMap (f : R.Space) : ((Φ f).val : Q → ℂ) =ᵐ[μQ] hform f :=
  (mDesc f).coeFn_toLp

omit hHaar in
theorem isGeneralLinearFormClass_classMap (f : R.Space) :
    IsGeneralLinearFormClass F r T i (Φ f : Lp ℂ 2 μQ) (R.realization.toContinuous f) :=
  ⟨hform f, descended_pullback F r T i R hdesc f, coeFn_classMap F r T i R hdesc hi I e hc hPD f⟩

/-- Quotient Haar measure is positive on every nonempty open set, so taking the class loses
no information about a continuous representative. -/
theorem classMap_injective : Function.Injective Φ := by
  let _ := positiveRationalQuotient_borelSpace F GLG T i hi I e hc
  have := haarQuotientMeasure_isOpenPosMeasure F GLG T i hi I e hc
  intro f g h
  apply descended_injective F r T i R hdesc
  have heq : (hform f : Q → ℂ) =ᵐ[μQ] hform g := by
    refine (coeFn_classMap F r T i R hdesc hi I e hc hPD f).symm.trans ?_
    rw [h]
    exact coeFn_classMap F r T i R hdesc hi I e hc hPD g
  exact ContinuousMap.coe_injective
    (((hform f).continuous.ae_eq_iff_eq μQ (hform g).continuous).mp heq)

/-- The continuous representative of a translate is the corresponding pullback on `Q`. -/
theorem coeFn_rightTranslate_classMap (a : AdelicGroupPoints F GLG) (f : R.Space) :
    ((πc a (Φ f)).val : Q → ℂ) =ᵐ[μQ]
      fun q => hform f (LeftCosetSpace.rightTranslate ΓQ a q) := by
  refine (coeFn_quotientL2RightTranslate F GLG T i μQ hR a (Φ f).val).trans ?_
  exact (hR a).quasiMeasurePreserving.ae (coeFn_classMap F r T i R hdesc hi I e hc hPD f)

set_option maxHeartbeats 800000 in
private theorem classMap_intertwine_of_toQuotient (a : AdelicGL F n) (f f' : R.Space)
    (h : ∀ q, OperatorDeterminantSlice.toQuotient F n R.realization f' q =
      OperatorDeterminantSlice.toQuotient F n R.realization f
        (OperatorDeterminantSlice.translate F n a q)) :
    Φ f' = πc ((aGL).symm a) (Φ f) := by
  apply Subtype.ext
  apply Lp.ext
  refine (coeFn_classMap F r T i R hdesc hi I e hc hPD f').trans ?_
  refine Filter.EventuallyEq.trans ?_
    (coeFn_rightTranslate_classMap F r T i R hdesc hi I e hc hPD ((aGL).symm a) f).symm
  apply ae_of_all
  intro q
  obtain ⟨q, rfl⟩ := projection_surjective F n T i q
  have hq := h q
  rw [toQuotient_eq_descended F r T i R hdesc, toQuotient_eq_descended F r T i R hdesc,
    projection_translate F r T i] at hq
  exact hq

/-- Finite adelic operators are carried to the original quotient action. -/
theorem classMap_finite (d : FiniteAdelicGL F n) (f : R.Space) :
    Φ (R.realization.finiteRepresentation d f) = πc ((aGL).symm (AdelicGL.ofFinite F n d)) (Φ f) :=
  classMap_intertwine_of_toQuotient F r T i R hdesc hi I e hc hPD _ f _
    (OperatorDeterminantSlice.toQuotient_finite F n R.realization d f)

/-- The archimedean compact operators are carried to the original quotient action. -/
theorem classMap_compact (k : standardInfiniteCompact F n) (f : R.Space) :
    Φ (R.realization.compactRepresentation k f) =
      πc ((aGL).symm (AdelicGL.ofInfinite F n k.val)) (Φ f) :=
  classMap_intertwine_of_toQuotient F r T i R hdesc hi I e hc hPD _ f _
    (OperatorDeterminantSlice.toQuotient_compact F n R.realization k f)

local notation "HB" => CuspidalHilbertOrbitCoefficient.BandHilbertSpace F r

omit [CompactSpace (AdeleQuotient F)] hHaar in
private theorem memLp_bandPullback (hc' : cB ≠ ⊤) (w : S) :
    MemLp ((w.val : Q → ℂ) ∘ pQ) 2 μB :=
  memLp_comp_projection F n T i hi I e hc hc' _ (Lp.memLp w.val)

/-- The class of a quotient `L²` vector pulled back to the band. -/
def bandPullback (hc' : cB ≠ ⊤) (w : S) : HB :=
  (memLp_bandPullback F r T i hi I e hc hPD hc' w).toLp ((w.val : Q → ℂ) ∘ pQ)

set_option maxHeartbeats 1000000 in
/-- The band pairings with the actual translated forms are the original quotient matrix
coefficients multiplied by the comparison constant. -/
theorem inner_bandPullback_translated (hc' : cB ≠ ⊤) (w : S) (a : AdelicGL F n) (f : R.Space) :
    ⟪bandPullback F r T i hi I e hc hPD hc' w,
      OperatorDeterminantSlice.translatedToL2 R.realization R.cuspidal a f⟫ =
      (cB).toReal • ⟪w, πc ((aGL).symm a) (Φ f)⟫ := by
  let _ := positiveRationalQuotient_borelSpace F GLG T i hi I e hc
  let g : Q → ℂ := fun q => ⟪w.val q, hform f (LeftCosetSpace.rightTranslate ΓQ ((aGL).symm a) q)⟫
  have hg : AEStronglyMeasurable g μQ :=
    (Lp.stronglyMeasurable w.val).aestronglyMeasurable.inner
      ((hform f).continuous.aestronglyMeasurable.comp_quasiMeasurePreserving
        (hR ((aGL).symm a)).quasiMeasurePreserving)
  rw [OperatorDeterminantSlice.inner_translatedToL2_left]
  trans ∫ q, g (pQ q) ∂μB
  · apply integral_congr_ae
    filter_upwards [(memLp_bandPullback F r T i hi I e hc hPD hc' w).coeFn_toLp] with q hq
    change ⟪((memLp_bandPullback F r T i hi I e hc hPD hc' w).toLp _) q, _⟫ = _
    rw [hq, toQuotient_eq_descended F r T i R hdesc, projection_translate F r T i]
    rfl
  · rw [CuspidalHilbertOrbitCoefficient.bandMeasure, integral_band F n T i hi I e hc g hg]
    congr 1
    rw [Submodule.coe_inner, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [coeFn_rightTranslate_classMap F r T i R hdesc hi I e hc hPD ((aGL).symm a) f]
      with q hq
    exact congrArg (Inner.inner ℂ (w.val q)) hq.symm

end Langlands.Automorphic.RealizationSummand
