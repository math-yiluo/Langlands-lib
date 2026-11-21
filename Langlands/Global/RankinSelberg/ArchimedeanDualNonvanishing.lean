import Langlands.Global.RankinSelberg.EqualInfinitePlaceTests
import Langlands.Global.RankinSelberg.EqualSemilocalReduction
import Langlands.Global.RankinSelberg.ArchimedeanCentralSignProof
import Langlands.Global.RankinSelberg.ArchimedeanFunctionalEquationStatement

/-! # Nonvanishing carried through an archimedean functional equation -/

noncomputable section
open Filter NumberField MeasureTheory
open scoped Classical Topology CategoryTheory.MonObj
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.LocalFactor Langlands.LocalFactor.Archimedean ArchimedeanLocal
open Langlands.Automorphic Langlands.Global.HeckeFunctionalEquation

universe u

attribute [local instance] archimedeanRealQMeasurable archimedeanRealQBorel
  archimedeanComplexQMeasurable archimedeanComplexQBorel
  archimedeanRealGLMeasurable archimedeanRealGLBorel archimedeanComplexGLMeasurable
  archimedeanComplexGLBorel archimedeanRealNMeasurable archimedeanRealNBorel
  archimedeanComplexNMeasurable archimedeanComplexNBorel

private theorem reciprocal_reflected_ne_zero (L : ReciprocalEntire) :
    ∀ᶠ s in codiscrete ℂ, (L.denominator (1 - s))⁻¹ ≠ 0 := by
  let R (s : ℂ) := L.denominator (1 - s)
  have hR : Differentiable ℂ R := L.entire.comp ((differentiable_const 1).sub differentiable_id)
  obtain ⟨z, hz⟩ := L.nonzero
  have hne : R (1 - z) ≠ 0 := by
    simpa only [R, sub_sub_cancel] using hz
  exact (EqualSemilocalReduction.eventually_ne_zero_of_analyticAt
    (fun s _ => (hR.analyticAt s).meromorphicAt) (hR.analyticAt (1 - z)) hne).mono
    fun _ hs => inv_ne_zero hs

/-- A nonzero ordinary integral and the analytic continuation identity give a nonzero
dual integral on its own right half-plane. The epsilon factor takes values in units. -/
theorem holomorphicNonzero_dual_of_functionalEquation
    {f g M Md A : ℂ → ℂ} (σ : ℝ) (Ldual : ReciprocalEntire)
    (ε : ℂ → ℂˣ) (c : ℂ) (hc : c ≠ 0)
    (hf : HolomorphicNonzeroOnRightHalfPlane f)
    (hfσ : DifferentiableOn ℂ f {s : ℂ | σ < s.re})
    (hgσ : DifferentiableOn ℂ g {s : ℂ | σ < s.re})
    (hM : MeromorphicOn M Set.univ)
    (hord : ∀ s : ℂ, σ < s.re → f s = M s)
    (hdual : ∀ s : ℂ, σ < s.re → g s = Md s)
    (hFE : ∀ᶠ s in codiscrete ℂ,
      A s * Md (1 - s) = c * (ε s : ℂ) * (Ldual.denominator (1 - s))⁻¹ * M s) :
    HolomorphicNonzeroOnRightHalfPlane g := by
  refine ⟨σ, hgσ, ?_⟩
  obtain ⟨z, hz, hzne⟩ := hf.exists_ne_zero_above σ
  have hop : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hdM : DifferentiableOn ℂ M {s : ℂ | σ < s.re} :=
    hfσ.congr fun s hs => (hord s hs).symm
  have hMan := hdM.analyticOnNhd hop z hz
  have hMne : ∀ᶠ s in codiscrete ℂ, M s ≠ 0 :=
    EqualSemilocalReduction.eventually_ne_zero_of_analyticAt hM hMan
      (fun h => hzne ((hord z hz).trans h))
  let w : ℂ := 1 - ((σ + 1 : ℝ) : ℂ)
  have hw : σ < (1 - w).re := by
    simp only [w, sub_sub_cancel, Complex.ofReal_re]
    linarith
  have hopen : IsOpen {s : ℂ | σ < (1 - s).re} :=
    hop.preimage (continuous_const.sub continuous_id)
  have hrightAt : ∀ᶠ s in 𝓝 w, σ < (1 - s).re := hopen.mem_nhds hw
  have hright : ∀ᶠ s in 𝓝[≠] w, σ < (1 - s).re :=
    hrightAt.filter_mono nhdsWithin_le_nhds
  have hreg := (reciprocal_reflected_ne_zero Ldual).and (hMne.and hFE)
  have hs := hright.and (hreg.filter_mono (nhdsNE_le_codiscrete w))
  obtain ⟨s, hsσ, hL, hMs, hrel⟩ := hs.exists
  refine ⟨1 - s, hsσ, fun hzero => ?_⟩
  have hMd : Md (1 - s) = 0 := (hdual (1 - s) hsσ).symm.trans hzero
  rw [hMd, mul_zero] at hrel
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero hc (ε s).ne_zero) hL) hMs) hrel.symm

section ActualTests

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  (ψ : Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
  (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
  {r : ℕ} (T Td T' Td' : CuspidalOperatorRealization F r)
  (hTd : OperatorRealization.IsContragredientOf Td.realization T.realization)
  (hTd' : OperatorRealization.IsContragredientOf Td'.realization T'.realization)

include hψ hTd hTd' in
/-- At a real place, the same test with a nonzero ordinary integral has a nonzero
dual integral once the local equal-rank functional equation is available. -/
theorem realEqualDualNonvanishing_of_equation (hFE : RealEqualFunctionalEquationStatement.{u})
    (v : {v : InfinitePlace F // v.IsReal}) (a : ℝˣ)
    (ha : IsRealAdditiveComponent ψ v.1 v.2 a)
    (d d' dd dd' : List RealBlock)
    (hd : T.realization.HasRealPlaceParameter v d) (hd' : T'.realization.HasRealPlaceParameter v d')
    (hdd : Td.realization.HasRealPlaceParameter v dd) (hdd' : Td'.realization.HasRealPlaceParameter v dd')
    (D : RealQuotientMeasureData r) (W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ)
    (hW : IsRealPlaceWhittaker F T ψ.complex v W)
    (hW' : IsRealPlaceWhittaker F T' ψ.complex⁻¹ v W')
    (hn : HolomorphicNonzeroOnRightHalfPlane (realEqualIntegral D W W' Φ)) :
    HolomorphicNonzeroOnRightHalfPlane (realEqualDualIntegral a D W W' Φ) := by
  obtain ⟨σ, M, Md, _, _, hdiff, hdiff', hM, _, ho, hdu, he⟩ :=
    hFE F ψ hψ r T Td T' Td' hTd hTd' v a ha d d' dd dd' hd hd' hdd hdd' D W W' Φ hW hW'
  obtain ⟨χ, hχ, _⟩ := T'.realization.existsUnique_hasCentralCharacter T'.irreducible
  have hsign : realMinusOneScalar T' v ≠ 0 := by
    rw [CentralSign.realMinusOneScalar_eq T' χ hχ v]
    exact Units.ne_zero _
  exact holomorphicNonzero_dual_of_functionalEquation σ (realPairLFactor dd dd')
    (realPairEpsilon d d' a (NNReal.sqrt ‖(a : ℝ)‖₊)
      (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)))
    (realMinusOneScalar T' v ^ r) (pow_ne_zero r hsign) hn hdiff hdiff' hM ho hdu he

include hψ hTd hTd' in
/-- The corresponding transfer at a complex place uses its own quotient measure
and its prescribed Fourier transform. -/
theorem complexEqualDualNonvanishing_of_equation (hFE : ComplexEqualFunctionalEquationStatement.{u})
    (w : {w : InfinitePlace F // w.IsComplex}) (a : ℂˣ)
    (ha : IsComplexAdditiveComponent ψ w.1 w.2 a)
    (d d' dd dd' : List ComplexCharacterData)
    (hd : T.realization.HasComplexPlaceParameter w d) (hd' : T'.realization.HasComplexPlaceParameter w d')
    (hdd : Td.realization.HasComplexPlaceParameter w dd) (hdd' : Td'.realization.HasComplexPlaceParameter w dd')
    (D : ComplexQuotientMeasureData r) (W W' : Langlands.GeneralLinear (r + 1) ℂ → ℂ)
    (Φ : SchwartzMap (Fin (r + 1) → ℂ) ℂ)
    (hW : IsComplexPlaceWhittaker F T ψ.complex w W)
    (hW' : IsComplexPlaceWhittaker F T' ψ.complex⁻¹ w W')
    (hn : HolomorphicNonzeroOnRightHalfPlane (complexEqualIntegral D W W' Φ)) :
    HolomorphicNonzeroOnRightHalfPlane (complexEqualDualIntegral a D W W' Φ) := by
  obtain ⟨σ, M, Md, _, _, hdiff, hdiff', hM, _, ho, hdu, he⟩ :=
    hFE F ψ hψ r T Td T' Td' hTd hTd' w a ha d d' dd dd' hd hd' hdd hdd' D W W' Φ hW hW'
  obtain ⟨χ, hχ, _⟩ := T'.realization.existsUnique_hasCentralCharacter T'.irreducible
  have hsign : complexMinusOneScalar T' w ≠ 0 := by
    rw [CentralSign.complexMinusOneScalar_eq T' χ hχ w]
    exact Units.ne_zero _
  exact holomorphicNonzero_dual_of_functionalEquation σ (complexPairLFactor dd dd')
    (complexPairEpsilon d d' a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero))
    (complexMinusOneScalar T' w ^ r) (pow_ne_zero r hsign) hn hdiff hdiff' hM ho hdu he

end ActualTests

end Langlands.Global.RankinSelbergGlobal
