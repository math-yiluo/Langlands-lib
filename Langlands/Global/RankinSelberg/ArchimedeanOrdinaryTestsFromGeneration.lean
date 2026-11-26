import Langlands.Global.RankinSelberg.ArchimedeanFactorizationOrdinaryReduction
import Langlands.Global.RankinSelberg.ArchimedeanOrdinaryNormalizedTests
import Langlands.Global.RankinSelberg.ArchimedeanPlaceWhittakerModels
import Langlands.Global.RankinSelberg.CuspidalWhittakerIdentityNonzero
import Langlands.Automorphic.CuspidalArchimedeanComponentIrreducibleProof
import Langlands.Global.RankinSelberg.ArchimedeanQuotientMeasures

/-! # Ordinary archimedean tests from local generation and restriction surjectivity

The four ordinary nonvanishing assertions used by
`ArchimedeanFactorizationOrdinaryReductionStatement` follow from normalized generation in the
local Whittaker models (`RealOrdinaryNormalizedGenerationStatement`,
`ComplexOrdinaryNormalizedGenerationStatement`; Jacquet 2009, Theorems 2.3, 2.6, 2.7) and from
the surjectivity of actual restrictions onto those models, stated here for every actual
cuspidal realization. Hence `ArchimedeanFactorizationStatement` follows from the slice
comparison, the real-place functional equation, the two generation statements and the two
surjectivity statements. See the paired Markdown.
-/

noncomputable section
open NumberField
open scoped CategoryTheory.MonObj
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u uQ

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Automorphic Langlands.LocalFactor Langlands.LocalFactor.Archimedean ArchimedeanLocal
open Langlands.Global.HeckeFunctionalEquation

attribute [local instance] archimedeanRealQMeasurable archimedeanRealQBorel
  archimedeanComplexQMeasurable archimedeanComplexQBorel
  archimedeanRealGLMeasurable archimedeanRealGLBorel archimedeanComplexGLMeasurable
  archimedeanComplexGLBorel archimedeanRealNMeasurable archimedeanRealNBorel
  archimedeanComplexNMeasurable archimedeanComplexNBorel

local notation "RP" F => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" F => {w : InfinitePlace F // InfinitePlace.IsComplex w}

/-- Every function of the specified real local Whittaker model is an actual restriction of a
global Whittaker function, for every actual cuspidal realization with that parameter. -/
def RealPlaceWhittakerRestrictionOntoStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r : ℕ) (T : CuspidalOperatorRealization F r) (v : RP F) (a : ℝˣ),
    IsRealAdditiveComponent ψ v.1 v.2 a →
  ∀ d : List RealBlock, T.realization.HasRealPlaceParameter v d →
  ∀ W : Langlands.GeneralLinear (r + 1) ℝ → ℂ,
    (W ∈ realWhittakerModel r d a → IsRealPlaceWhittaker F T ψ.complex v W) ∧
    (W ∈ realWhittakerModel r d (-a) → IsRealPlaceWhittaker F T ψ.complex⁻¹ v W)

/-- The corresponding assertion at a complex place. -/
def ComplexPlaceWhittakerRestrictionOntoStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r : ℕ) (T : CuspidalOperatorRealization F r) (w : CP F) (a : ℂˣ),
    IsComplexAdditiveComponent ψ w.1 w.2 a →
  ∀ d : List ComplexCharacterData, T.realization.HasComplexPlaceParameter w d →
  ∀ W : Langlands.GeneralLinear (r + 1) ℂ → ℂ,
    (W ∈ complexWhittakerModel r d a → IsComplexPlaceWhittaker F T ψ.complex w W) ∧
    (W ∈ complexWhittakerModel r d (-a) → IsComplexPlaceWhittaker F T ψ.complex⁻¹ w W)

section Models

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

omit [CompactSpace (AdeleQuotient F)] in
private theorem adelicPoint_one_one (n : ℕ) : adelicPoint F n 1 1 = 1 := by
  unfold adelicPoint
  rw [map_one]
  change (GeneralLinearGroupPoints.adelicEquiv F n).symm (AdelicGL.ofFinite F n 1) = 1
  rw [map_one, map_one]

omit [CompactSpace (AdeleQuotient F)] in
private theorem realPlacePoint_one_mul (n : ℕ) (v : RP F) :
    realPlacePoint F n v 1 * finitePoint F n 1 = 1 := by
  unfold realPlacePoint finitePoint
  rw [map_one, adelicPoint_one_one, one_mul]

omit [CompactSpace (AdeleQuotient F)] in
private theorem complexPlacePoint_one_mul (n : ℕ) (w : CP F) :
    complexPlacePoint F n w 1 * finitePoint F n 1 = 1 := by
  unfold complexPlacePoint finitePoint
  rw [map_one, adelicPoint_one_one, one_mul]

omit [CompactSpace (AdeleQuotient F)] in
private theorem inverse_standard (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) :
    IsStandardAdditiveCharacter F ψ.complex⁻¹ := by
  have hψ' (x : F) : inverseCharacter ψ (algebraMap F (Adeles F) x) = 1 := by
    rw [inverseCharacter_apply, hψ, inv_one]
  simpa only [complex_inverseCharacter] using
    UnramifiedWhittaker.isStandardAdditiveCharacter_complex F (inverseCharacter ψ) hψ'

/-- The real local Whittaker models of an actual parameter, for the component of `ψ` and for
its inverse, are nonzero: they contain the restriction of a vector whose global Whittaker
function is nonzero at the identity. -/
theorem realWhittakerModel_ne_bot (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) {r : ℕ} (T : CuspidalOperatorRealization F r)
    (v : RP F) (a : ℝˣ) (ha : IsRealAdditiveComponent ψ v.1 v.2 a) {d : List RealBlock}
    (hd : T.realization.HasRealPlaceParameter v d) :
    realWhittakerModel r d a ≠ ⊥ ∧ realWhittakerModel r d (-a) ≠ ⊥ := by
  constructor
  · obtain ⟨x, hx⟩ := cuspidalWhittakerIdentityNonzero F r T ψ.complex
      (UnramifiedWhittaker.isStandardAdditiveCharacter_complex F ψ hψ)
    let W : Langlands.GeneralLinear (r + 1) ℝ → ℂ := fun g =>
      cuspWhittaker F T ψ.complex x (realPlacePoint F (r + 1) v g * finitePoint F (r + 1) 1)
    have hmem : W ∈ realWhittakerModel r d a := RealUniformWhittaker.model_le_model d a
      ((archimedeanPlaceWhittakerModels.1 F ψ hψ r T v a ha d hd W).1 ⟨x, 1, rfl⟩)
    intro hbot
    rw [hbot, Submodule.mem_bot] at hmem
    apply hx
    have h1 := congrFun hmem 1
    simpa only [W, realPlacePoint_one_mul, Pi.zero_apply] using h1
  · obtain ⟨x, hx⟩ := cuspidalWhittakerIdentityNonzero F r T ψ.complex⁻¹ (inverse_standard ψ hψ)
    let W : Langlands.GeneralLinear (r + 1) ℝ → ℂ := fun g =>
      cuspWhittaker F T ψ.complex⁻¹ x (realPlacePoint F (r + 1) v g * finitePoint F (r + 1) 1)
    have hmem : W ∈ realWhittakerModel r d (-a) := RealUniformWhittaker.model_le_model d (-a)
      ((archimedeanPlaceWhittakerModels.1 F ψ hψ r T v a ha d hd W).2 ⟨x, 1, rfl⟩)
    intro hbot
    rw [hbot, Submodule.mem_bot] at hmem
    apply hx
    have h1 := congrFun hmem 1
    simpa only [W, realPlacePoint_one_mul, Pi.zero_apply] using h1

/-- The complex local Whittaker models of an actual parameter, for the component of `ψ` and
for its inverse, are nonzero. -/
theorem complexWhittakerModel_ne_bot (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) {r : ℕ} (T : CuspidalOperatorRealization F r)
    (w : CP F) (a : ℂˣ) (ha : IsComplexAdditiveComponent ψ w.1 w.2 a)
    {d : List ComplexCharacterData} (hd : T.realization.HasComplexPlaceParameter w d) :
    complexWhittakerModel r d a ≠ ⊥ ∧ complexWhittakerModel r d (-a) ≠ ⊥ := by
  constructor
  · obtain ⟨x, hx⟩ := cuspidalWhittakerIdentityNonzero F r T ψ.complex
      (UnramifiedWhittaker.isStandardAdditiveCharacter_complex F ψ hψ)
    let W : Langlands.GeneralLinear (r + 1) ℂ → ℂ := fun g =>
      cuspWhittaker F T ψ.complex x (complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) 1)
    have hmem : W ∈ complexWhittakerModel r d a :=
      (archimedeanPlaceWhittakerModels.2 F ψ hψ r T w a ha d hd W).1 ⟨x, 1, rfl⟩
    intro hbot
    rw [hbot, Submodule.mem_bot] at hmem
    apply hx
    have h1 := congrFun hmem 1
    simpa only [W, complexPlacePoint_one_mul, Pi.zero_apply] using h1
  · obtain ⟨x, hx⟩ := cuspidalWhittakerIdentityNonzero F r T ψ.complex⁻¹ (inverse_standard ψ hψ)
    let W : Langlands.GeneralLinear (r + 1) ℂ → ℂ := fun g =>
      cuspWhittaker F T ψ.complex⁻¹ x (complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) 1)
    have hmem : W ∈ complexWhittakerModel r d (-a) :=
      (archimedeanPlaceWhittakerModels.2 F ψ hψ r T w a ha d hd W).2 ⟨x, 1, rfl⟩
    intro hbot
    rw [hbot, Submodule.mem_bot] at hmem
    apply hx
    have h1 := congrFun hmem 1
    simpa only [W, complexPlacePoint_one_mul, Pi.zero_apply] using h1

end Models

section LocalTests

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
  (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)

include hψ in
/-- Unequal ranks at a real place: if every function of the two specified local models is an
actual restriction, real generation gives an actual pair with nonzero ordinary integral at
points arbitrarily far to the right. -/
theorem exists_realUnequalOrdinaryTest (hG : RealOrdinaryNormalizedGenerationStatement)
    {r t : ℕ} (h : t < r) (T : CuspidalOperatorRealization F r)
    (T' : CuspidalOperatorRealization F t) (v : RP F) (a : ℝˣ)
    (ha : IsRealAdditiveComponent ψ v.1 v.2 a) {d d' : List RealBlock}
    (hd : T.realization.HasRealPlaceParameter v d) (hd' : T'.realization.HasRealPlaceParameter v d')
    (hS : ∀ W, W ∈ realWhittakerModel r d a → IsRealPlaceWhittaker F T ψ.complex v W)
    (hS' : ∀ W, W ∈ realWhittakerModel t d' (-a) → IsRealPlaceWhittaker F T' ψ.complex⁻¹ v W) :
    ∃ (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ)
      (D : RealQuotientMeasureData t),
      IsRealPlaceWhittaker F T ψ.complex v W ∧ IsRealPlaceWhittaker F T' ψ.complex⁻¹ v W' ∧
      ∀ σ : ℝ, ∃ s : ℂ, σ < s.re ∧ realUnequalIntegral h D W W' s ≠ 0 := by
  obtain ⟨i, N, hN⟩ := (hG.1 r t h d d' hd.1 hd'.1 (T.isIrreducibleRealStandard v d hd)
    (T'.isIrreducibleRealStandard v d' hd') a (realQuotientMeasureData t)
    (realWhittakerModel_ne_bot ψ hψ T v a ha hd).1
    (realWhittakerModel_ne_bot ψ hψ T' v a ha hd').2).1 0
  exact ⟨i.1, i.2, realQuotientMeasureData t, hS _ i.1.2, hS' _ i.2.2,
    fun σ => OrdinaryIntegralNormalization.exists_ne_zero_above _ N hN σ⟩

include hψ in
/-- Equal ranks at a real place, under the same surjectivity hypotheses. -/
theorem exists_realEqualOrdinaryTest (hG : RealOrdinaryNormalizedGenerationStatement)
    {r : ℕ} (T T' : CuspidalOperatorRealization F r) (v : RP F) (a : ℝˣ)
    (ha : IsRealAdditiveComponent ψ v.1 v.2 a) {d d' : List RealBlock}
    (hd : T.realization.HasRealPlaceParameter v d) (hd' : T'.realization.HasRealPlaceParameter v d')
    (hS : ∀ W, W ∈ realWhittakerModel r d a → IsRealPlaceWhittaker F T ψ.complex v W)
    (hS' : ∀ W, W ∈ realWhittakerModel r d' (-a) → IsRealPlaceWhittaker F T' ψ.complex⁻¹ v W) :
    ∃ (W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
      (Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ) (D : RealQuotientMeasureData r),
      IsRealPlaceWhittaker F T ψ.complex v W ∧ IsRealPlaceWhittaker F T' ψ.complex⁻¹ v W' ∧
      ∀ σ : ℝ, ∃ s : ℂ, σ < s.re ∧ realEqualIntegral D W W' Φ s ≠ 0 := by
  obtain ⟨i, N, hN⟩ := (hG.2 r d d' hd.1 hd'.1 (T.isIrreducibleRealStandard v d hd)
    (T'.isIrreducibleRealStandard v d' hd') a (realQuotientMeasureData r)
    (realWhittakerModel_ne_bot ψ hψ T v a ha hd).1
    (realWhittakerModel_ne_bot ψ hψ T' v a ha hd').2).1 0
  exact ⟨i.1, i.2.1, i.2.2, realQuotientMeasureData r, hS _ i.1.2, hS' _ i.2.1.2,
    fun σ => OrdinaryIntegralNormalization.exists_ne_zero_above _ N hN σ⟩

include hψ in
/-- Unequal ranks at a complex place, under the corresponding surjectivity hypotheses. -/
theorem exists_complexUnequalOrdinaryTest (hG : ComplexOrdinaryNormalizedGenerationStatement)
    {r t : ℕ} (h : t < r) (T : CuspidalOperatorRealization F r)
    (T' : CuspidalOperatorRealization F t) (w : CP F) (a : ℂˣ)
    (ha : IsComplexAdditiveComponent ψ w.1 w.2 a) {d d' : List ComplexCharacterData}
    (hd : T.realization.HasComplexPlaceParameter w d)
    (hd' : T'.realization.HasComplexPlaceParameter w d')
    (hS : ∀ W, W ∈ complexWhittakerModel r d a → IsComplexPlaceWhittaker F T ψ.complex w W)
    (hS' : ∀ W, W ∈ complexWhittakerModel t d' (-a) →
      IsComplexPlaceWhittaker F T' ψ.complex⁻¹ w W) :
    ∃ (W : Langlands.GeneralLinear (r + 1) ℂ → ℂ) (W' : Langlands.GeneralLinear (t + 1) ℂ → ℂ)
      (D : ComplexQuotientMeasureData t),
      IsComplexPlaceWhittaker F T ψ.complex w W ∧ IsComplexPlaceWhittaker F T' ψ.complex⁻¹ w W' ∧
      ∀ σ : ℝ, ∃ s : ℂ, σ < s.re ∧ complexUnequalIntegral h D W W' s ≠ 0 := by
  obtain ⟨i, N, hN⟩ := (hG.1 r t h d d' hd.1 hd'.1 (T.isIrreducibleComplexStandard w d hd)
    (T'.isIrreducibleComplexStandard w d' hd') a (complexQuotientMeasureData t)
    (complexWhittakerModel_ne_bot ψ hψ T w a ha hd).1
    (complexWhittakerModel_ne_bot ψ hψ T' w a ha hd').2).1 0
  exact ⟨i.1, i.2, complexQuotientMeasureData t, hS _ i.1.2, hS' _ i.2.2,
    fun σ => OrdinaryIntegralNormalization.exists_ne_zero_above _ N hN σ⟩

include hψ in
/-- Equal ranks at a complex place, under the corresponding surjectivity hypotheses. -/
theorem exists_complexEqualOrdinaryTest (hG : ComplexOrdinaryNormalizedGenerationStatement)
    {r : ℕ} (T T' : CuspidalOperatorRealization F r) (w : CP F) (a : ℂˣ)
    (ha : IsComplexAdditiveComponent ψ w.1 w.2 a) {d d' : List ComplexCharacterData}
    (hd : T.realization.HasComplexPlaceParameter w d)
    (hd' : T'.realization.HasComplexPlaceParameter w d')
    (hS : ∀ W, W ∈ complexWhittakerModel r d a → IsComplexPlaceWhittaker F T ψ.complex w W)
    (hS' : ∀ W, W ∈ complexWhittakerModel r d' (-a) →
      IsComplexPlaceWhittaker F T' ψ.complex⁻¹ w W) :
    ∃ (W W' : Langlands.GeneralLinear (r + 1) ℂ → ℂ)
      (Φ : SchwartzMap (Fin (r + 1) → ℂ) ℂ) (D : ComplexQuotientMeasureData r),
      IsComplexPlaceWhittaker F T ψ.complex w W ∧ IsComplexPlaceWhittaker F T' ψ.complex⁻¹ w W' ∧
      ∀ σ : ℝ, ∃ s : ℂ, σ < s.re ∧ complexEqualIntegral D W W' Φ s ≠ 0 := by
  obtain ⟨i, N, hN⟩ := (hG.2 r d d' hd.1 hd'.1 (T.isIrreducibleComplexStandard w d hd)
    (T'.isIrreducibleComplexStandard w d' hd') a (complexQuotientMeasureData r)
    (complexWhittakerModel_ne_bot ψ hψ T w a ha hd).1
    (complexWhittakerModel_ne_bot ψ hψ T' w a ha hd').2).1 0
  exact ⟨i.1, i.2.1, i.2.2, complexQuotientMeasureData r, hS _ i.1.2, hS' _ i.2.1.2,
    fun σ => OrdinaryIntegralNormalization.exists_ne_zero_above _ N hN σ⟩

end LocalTests

/-- Real ordinary nonvanishing in both rank cases from real normalized generation and real
restriction surjectivity. -/
theorem realOrdinaryPlaceTests_of_generation (hG : RealOrdinaryNormalizedGenerationStatement)
    (hS : RealPlaceWhittakerRestrictionOntoStatement.{u}) :
    RealUnequalOrdinaryPlaceTestsStatement.{u} ∧
      RealEqualOrdinaryPlaceTestsPositiveRankStatement.{u} :=
  ⟨fun F _ _ _ ψ hψ r t h T T' v a ha _ _ hd hd' =>
    exists_realUnequalOrdinaryTest ψ hψ hG h T T' v a ha hd hd'
      (fun W => (hS F ψ hψ r T v a ha _ hd W).1) (fun W => (hS F ψ hψ t T' v a ha _ hd' W).2),
    fun F _ _ _ ψ hψ r _ T T' v a ha _ _ hd hd' =>
    exists_realEqualOrdinaryTest ψ hψ hG T T' v a ha hd hd'
      (fun W => (hS F ψ hψ r T v a ha _ hd W).1) (fun W => (hS F ψ hψ r T' v a ha _ hd' W).2)⟩

/-- Complex ordinary nonvanishing in both rank cases from complex normalized generation and
complex restriction surjectivity. -/
theorem complexOrdinaryPlaceTests_of_generation (hG : ComplexOrdinaryNormalizedGenerationStatement)
    (hS : ComplexPlaceWhittakerRestrictionOntoStatement.{u}) :
    ComplexUnequalOrdinaryPlaceTestsStatement.{u} ∧
      ComplexEqualOrdinaryPlaceTestsPositiveRankStatement.{u} :=
  ⟨fun F _ _ _ ψ hψ r t h T T' w a ha _ _ hd hd' =>
    exists_complexUnequalOrdinaryTest ψ hψ hG h T T' w a ha hd hd'
      (fun W => (hS F ψ hψ r T w a ha _ hd W).1) (fun W => (hS F ψ hψ t T' w a ha _ hd' W).2),
    fun F _ _ _ ψ hψ r _ T T' w a ha _ _ hd hd' =>
    exists_complexEqualOrdinaryTest ψ hψ hG T T' w a ha hd hd'
      (fun W => (hS F ψ hψ r T w a ha _ hd W).1) (fun W => (hS F ψ hψ r T' w a ha _ hd' W).2)⟩

/-- **Conditional factorization from local generation.** The slice comparison, the real-place
functional equation, real and complex normalized generation and real and complex restriction
surjectivity imply `ArchimedeanFactorizationStatement`. -/
def ArchimedeanFactorizationGenerationReductionStatement : Prop :=
  InfiniteWhittakerSliceModelStatement.{u, uQ} → RealPlaceFunctionalEquationStatement.{u} →
    RealOrdinaryNormalizedGenerationStatement → ComplexOrdinaryNormalizedGenerationStatement →
    RealPlaceWhittakerRestrictionOntoStatement.{u} →
    ComplexPlaceWhittakerRestrictionOntoStatement.{u} →
    ArchimedeanFactorizationStatement.{u, uQ}

/-- Proof: the ordinary tests come from generation and surjectivity, and
`archimedeanFactorizationOrdinaryReduction` gives the target. -/
theorem archimedeanFactorizationGenerationReduction :
    ArchimedeanFactorizationGenerationReductionStatement.{u, uQ} :=
  fun hSlice hRealFE hGR hGC hSR hSC =>
    archimedeanFactorizationOrdinaryReduction hSlice hRealFE
      (realOrdinaryPlaceTests_of_generation hGR hSR).1
      (complexOrdinaryPlaceTests_of_generation hGC hSC).1
      (realOrdinaryPlaceTests_of_generation hGR hSR).2
      (complexOrdinaryPlaceTests_of_generation hGC hSC).2

end Langlands.Global.RankinSelbergGlobal
