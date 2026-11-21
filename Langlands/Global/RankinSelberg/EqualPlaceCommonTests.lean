import Langlands.Global.RankinSelberg.EqualInfinitePlaceTests
import Langlands.Global.RankinSelberg.EqualLocalCommonTest

/-! # A common equal-rank test from separate actual place witnesses -/

noncomputable section

open MeasureTheory NumberField
open Langlands.Automorphic Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open Langlands.Global.HeckeFunctionalEquation
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

universe u

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable archimedeanRealQBorel
  archimedeanComplexGLMeasurable archimedeanComplexGLBorel archimedeanComplexNMeasurable
  archimedeanComplexNBorel archimedeanComplexQMeasurable archimedeanComplexQBorel

namespace EqualPlaceCommonTests

private def restrictionMap {F : Type u} [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] {r : ℕ} (T : CuspidalOperatorRealization F r)
    (χ : AddChar (Adeles F) ℂ) (hχ : IsStandardAdditiveCharacter F χ)
    {G : Type*} (point : G → Points F (r + 1)) : T.Space →ₗ[ℂ] (G → ℂ) :=
  LinearMap.pi fun g => UnramifiedWhittaker.whittakerFunctional F χ hχ T (point g)

private theorem restriction_exists_iff {F : Type u} [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] {r : ℕ} (T : CuspidalOperatorRealization F r)
    (χ : AddChar (Adeles F) ℂ) (hχ : IsStandardAdditiveCharacter F χ)
    {G : Type*} (point : G → Points F (r + 1)) (W : G → ℂ) :
    (∃ (x : T.Space) (b : FiniteAdelicGL F (r + 1)),
      W = fun g => cuspWhittaker F T χ x (point g * finitePoint F (r + 1) b)) ↔
      ∃ x, restrictionMap T χ hχ point x = W := by
  have hfin (b : FiniteAdelicGL F (r + 1)) :
      finitePoint F (r + 1) b = (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm
        (AdelicGL.ofFinite F (r + 1) b) := by
    unfold finitePoint adelicPoint
    rw [map_one]
    rfl
  constructor
  · rintro ⟨x, b, rfl⟩
    refine ⟨T.realization.finiteRepresentation b x, funext fun g => ?_⟩
    rw [hfin]
    exact UnramifiedWhittaker.cuspWhittaker_finiteRepresentation F χ T b x (point g)
  · rintro ⟨x, rfl⟩
    have hOne : finitePoint F (r + 1) 1 = 1 := by
      simp [hfin, AdelicGL.ofFinite]
    exact ⟨x, 1, funext fun g => by simp [hOne, restrictionMap,
      UnramifiedWhittaker.whittakerFunctional]⟩

private def testMap {K : Type*} [NormedField K] [NormedAlgebra ℝ K] [FiniteDimensional ℝ K]
    [MeasurableSpace K] [BorelSpace K] [LocallyCompactSpace K] [SecondCountableTopology K]
    {n : ℕ} (χ : UnitaryAdditiveCharacter K) (ν : AdditiveHaarMeasure K) :
    Bool → SchwartzMap (Fin n → K) ℂ →+ ((Fin n → K) → ℂ)
  | false => {
      toFun := fun Φ => Φ
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  | true => {
      toFun := fun Φ => ArchimedeanLocal.fourierTransform χ.complex ν.measure Φ
      map_zero' := by
        funext x
        simp [ArchimedeanLocal.fourierTransform]
      map_add' := fun f g => by
        funext x
        have := ν.isAddHaar
        let measure := Measure.pi (fun _ : Fin n => ν.measure)
        have : measure.IsAddHaarMeasure := by dsimp [measure]; infer_instance
        let Kx (y : Fin n → K) := χ.complex (∑ j, y j * x j)
        have hK : Continuous Kx := χ.continuous_complex.comp
          (continuous_finsetSum _ fun j _ => (continuous_apply j).mul continuous_const)
        have hInt (Φ : SchwartzMap (Fin n → K) ℂ) :
            Integrable (fun y => Φ y * Kx y) measure :=
          Φ.integrable.mul_bdd hK.aestronglyMeasurable
            (Filter.Eventually.of_forall fun y => (χ.norm_complex _).le)
        change (∫ y, (f y + g y) * Kx y ∂measure) =
          (∫ y, f y * Kx y ∂measure) + (∫ y, g y * Kx y ∂measure)
        simpa only [add_mul] using integral_add (hInt f) (hInt g) }

private def coefficientMap {A K : Type*} [AddZeroClass A] [Field K] {r : ℕ}
    (L : A →+ (Langlands.GeneralLinear (r + 1) K → ℂ)) :
    Bool → A →+ (Langlands.GeneralLinear (r + 1) K → ℂ)
  | false => L
  | true => {
      toFun := fun x => ArchimedeanLocal.dualFunction (r + 1) (L x)
      map_zero' := by
        funext g
        simp [ArchimedeanLocal.dualFunction]
      map_add' := fun x y => by
        funext g
        simp [ArchimedeanLocal.dualFunction] }

private theorem exists_common_for_ranges {K A B C : Type*} [Field K] [TopologicalSpace K]
    [AddZeroClass A] [AddZeroClass B] [AddZeroClass C] {r : ℕ}
    [MeasurableSpace (Langlands.RankinSelberg.LeftUnipotentQuotient r K)]
    (nabs : K → ℝ) (measure : Measure (Langlands.RankinSelberg.LeftUnipotentQuotient r K))
    (L : A →+ (Langlands.GeneralLinear (r + 1) K → ℂ))
    (L' : B →+ (Langlands.GeneralLinear (r + 1) K → ℂ))
    (Φ : Bool → C →+ ((Fin (r + 1) → K) → ℂ))
    (hConverges : ∀ i x y z, ∃ σ : ℝ,
      (∀ s : ℂ, σ < s.re → Integrable
        (ArchimedeanLocal.equalIntegrand nabs
          (coefficientMap L i x) (coefficientMap L' i y) (Φ i z) s) measure) ∧
      DifferentiableOn ℂ
        (ArchimedeanLocal.equalIntegral nabs measure
          (coefficientMap L i x) (coefficientMap L' i y) (Φ i z))
        {s : ℂ | σ < s.re})
    (hNonzero : ∀ i, ∃ x y z, ∀ σ : ℝ, ∃ s : ℂ, σ < s.re ∧
      ArchimedeanLocal.equalIntegral nabs measure
        (coefficientMap L i x) (coefficientMap L' i y) (Φ i z) s ≠ 0) :
    ∃ x y z, ∀ i, HolomorphicNonzeroOnRightHalfPlane
      (ArchimedeanLocal.equalIntegral nabs measure
        (coefficientMap L i x) (coefficientMap L' i y) (Φ i z)) := by
  obtain ⟨x, y, z, h⟩ := EqualLocalCommonTest.exists_common_nonzero nabs measure
    (coefficientMap L) (coefficientMap L') Φ
    (fun i x y z => let ⟨σ, hσ, _⟩ := hConverges i x y z; ⟨σ, hσ⟩) hNonzero
  exact ⟨x, y, z, fun i => let ⟨σ, _, hσ⟩ := hConverges i x y z; ⟨σ, hσ, h i σ⟩⟩

section Actual

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    {r : ℕ} (T T' : CuspidalOperatorRealization F r)

include hψ in
/-- With a fixed quotient measure, actual ordinary and dual witnesses for a real
place can be combined into one ordinary and dual test. -/
theorem real (v : {v : InfinitePlace F // v.IsReal}) (a : ℝˣ)
    (D : RealQuotientMeasureData r)
    (hConverges : ∀ {W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
      (Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ),
      IsRealPlaceWhittaker F T ψ.complex v W → IsRealPlaceWhittaker F T' ψ.complex⁻¹ v W' →
      ∃ σ : ℝ, (∀ s : ℂ, σ < s.re → Integrable (realEqualIntegrand W W' Φ s) D.measure) ∧
        (∀ s : ℂ, σ < s.re → Integrable
          (realEqualIntegrand (ArchimedeanLocal.dualFunction (r + 1) W)
            (ArchimedeanLocal.dualFunction (r + 1) W')
            (realFourierTransform a Φ) s) D.measure) ∧
        DifferentiableOn ℂ (realEqualIntegral D W W' Φ) {s : ℂ | σ < s.re} ∧
        DifferentiableOn ℂ (realEqualDualIntegral a D W W' Φ) {s : ℂ | σ < s.re})
    (hNonzero : ∀ i : Bool, ∃ (W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
      (Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ),
      IsRealPlaceWhittaker F T ψ.complex v W ∧ IsRealPlaceWhittaker F T' ψ.complex⁻¹ v W' ∧
      (∀ σ : ℝ, ∃ s : ℂ, σ < s.re ∧
        (if i then realEqualDualIntegral a D W W' Φ s else realEqualIntegral D W W' Φ s) ≠ 0)) :
    ∃ (W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ),
      IsRealPlaceWhittaker F T ψ.complex v W ∧ IsRealPlaceWhittaker F T' ψ.complex⁻¹ v W' ∧
      HolomorphicNonzeroOnRightHalfPlane (realEqualIntegral D W W' Φ) ∧
      HolomorphicNonzeroOnRightHalfPlane (realEqualDualIntegral a D W W' Φ) := by
  have hχ := UnramifiedWhittaker.isStandardAdditiveCharacter_complex F ψ hψ
  have hχ' := Unfolding.isStandardAdditiveCharacter_inv F ψ.complex hχ
  let p := realPlacePoint F (r + 1) v
  let L := (restrictionMap T ψ.complex hχ p).toAddMonoidHom
  let L' := (restrictionMap T' ψ.complex⁻¹ hχ' p).toAddMonoidHom
  have hW (W) : IsRealPlaceWhittaker F T ψ.complex v W ↔ ∃ x, L x = W :=
    restriction_exists_iff T ψ.complex hχ p W
  have hW' (W') : IsRealPlaceWhittaker F T' ψ.complex⁻¹ v W' ↔ ∃ x, L' x = W' :=
    restriction_exists_iff T' ψ.complex⁻¹ hχ' p W'
  obtain ⟨x, y, Φ, h⟩ := exists_common_for_ranges realNormalizedAbs D.measure L L'
    (testMap (realScaledCharacter a) (realSelfDualMeasure a)) (fun i x y Φ => by
      obtain ⟨σ, hInt, hIntd, hHol, hHold⟩ :=
        hConverges Φ ((hW _).2 ⟨x, rfl⟩) ((hW' _).2 ⟨y, rfl⟩)
      cases i
      · exact ⟨σ, hInt, hHol⟩
      · exact ⟨σ, hIntd, hHold⟩) (fun i => by
        obtain ⟨W, W', Φ, hreal, hreal', hn⟩ := hNonzero i
        obtain ⟨x, rfl⟩ := (hW W).1 hreal
        obtain ⟨y, rfl⟩ := (hW' W').1 hreal'
        cases i <;> exact ⟨x, y, Φ, hn⟩)
  exact ⟨L x, L' y, Φ, (hW _).2 ⟨x, rfl⟩, (hW' _).2 ⟨y, rfl⟩, h false, h true⟩

include hψ in
/-- The analogous common test for actual restrictions at a complex place. -/
theorem complex (w : {w : InfinitePlace F // w.IsComplex}) (a : ℂˣ)
    (D : ComplexQuotientMeasureData r)
    (hConverges : ∀ {W W' : Langlands.GeneralLinear (r + 1) ℂ → ℂ}
      (Φ : SchwartzMap (Fin (r + 1) → ℂ) ℂ),
      IsComplexPlaceWhittaker F T ψ.complex w W → IsComplexPlaceWhittaker F T' ψ.complex⁻¹ w W' →
      ∃ σ : ℝ, (∀ s : ℂ, σ < s.re → Integrable (complexEqualIntegrand W W' Φ s) D.measure) ∧
        (∀ s : ℂ, σ < s.re → Integrable
          (complexEqualIntegrand (ArchimedeanLocal.dualFunction (r + 1) W)
            (ArchimedeanLocal.dualFunction (r + 1) W')
            (complexFourierTransform a Φ) s) D.measure) ∧
        DifferentiableOn ℂ (complexEqualIntegral D W W' Φ) {s : ℂ | σ < s.re} ∧
        DifferentiableOn ℂ (complexEqualDualIntegral a D W W' Φ) {s : ℂ | σ < s.re})
    (hNonzero : ∀ i : Bool, ∃ (W W' : Langlands.GeneralLinear (r + 1) ℂ → ℂ)
      (Φ : SchwartzMap (Fin (r + 1) → ℂ) ℂ),
      IsComplexPlaceWhittaker F T ψ.complex w W ∧ IsComplexPlaceWhittaker F T' ψ.complex⁻¹ w W' ∧
      (∀ σ : ℝ, ∃ s : ℂ, σ < s.re ∧
        (if i then complexEqualDualIntegral a D W W' Φ s else complexEqualIntegral D W W' Φ s) ≠ 0)) :
    ∃ (W W' : Langlands.GeneralLinear (r + 1) ℂ → ℂ) (Φ : SchwartzMap (Fin (r + 1) → ℂ) ℂ),
      IsComplexPlaceWhittaker F T ψ.complex w W ∧ IsComplexPlaceWhittaker F T' ψ.complex⁻¹ w W' ∧
      HolomorphicNonzeroOnRightHalfPlane (complexEqualIntegral D W W' Φ) ∧
      HolomorphicNonzeroOnRightHalfPlane (complexEqualDualIntegral a D W W' Φ) := by
  have hχ := UnramifiedWhittaker.isStandardAdditiveCharacter_complex F ψ hψ
  have hχ' := Unfolding.isStandardAdditiveCharacter_inv F ψ.complex hχ
  let p := complexPlacePoint F (r + 1) w
  let L := (restrictionMap T ψ.complex hχ p).toAddMonoidHom
  let L' := (restrictionMap T' ψ.complex⁻¹ hχ' p).toAddMonoidHom
  have hW (W) : IsComplexPlaceWhittaker F T ψ.complex w W ↔ ∃ x, L x = W :=
    restriction_exists_iff T ψ.complex hχ p W
  have hW' (W') : IsComplexPlaceWhittaker F T' ψ.complex⁻¹ w W' ↔ ∃ x, L' x = W' :=
    restriction_exists_iff T' ψ.complex⁻¹ hχ' p W'
  obtain ⟨x, y, Φ, h⟩ := exists_common_for_ranges complexNormalizedAbs D.measure L L'
    (testMap (complexScaledCharacter a) (complexSelfDualMeasure a)) (fun i x y Φ => by
      obtain ⟨σ, hInt, hIntd, hHol, hHold⟩ :=
        hConverges Φ ((hW _).2 ⟨x, rfl⟩) ((hW' _).2 ⟨y, rfl⟩)
      cases i
      · exact ⟨σ, hInt, hHol⟩
      · exact ⟨σ, hIntd, hHold⟩) (fun i => by
        obtain ⟨W, W', Φ, hcomplex, hcomplex', hn⟩ := hNonzero i
        obtain ⟨x, rfl⟩ := (hW W).1 hcomplex
        obtain ⟨y, rfl⟩ := (hW' W').1 hcomplex'
        cases i <;> exact ⟨x, y, Φ, hn⟩)
  exact ⟨L x, L' y, Φ, (hW _).2 ⟨x, rfl⟩, (hW' _).2 ⟨y, rfl⟩, h false, h true⟩

end Actual

end EqualPlaceCommonTests

end Langlands.Global.RankinSelbergGlobal
