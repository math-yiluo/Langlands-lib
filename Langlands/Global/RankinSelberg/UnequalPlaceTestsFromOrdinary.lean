import Langlands.Global.RankinSelberg.UnequalInfinitePlaceTests
import Langlands.Global.RankinSelberg.ArchimedeanFunctionalEquationStatement
import Langlands.Global.RankinSelberg.EqualSemilocalReduction
import Langlands.Global.RankinSelberg.OrdinarySemilocalNormalization

/-! # Dual unequal-rank test nonvanishing from the local functional equation -/

noncomputable section
open NumberField Filter
open scoped Classical CategoryTheory.MonObj Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

universe u

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Automorphic Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open Langlands.Global.HeckeFunctionalEquation ArchimedeanLocal

attribute [local instance] archimedeanRealQMeasurable archimedeanRealQBorel
  archimedeanComplexQMeasurable archimedeanComplexQBorel
  archimedeanRealGLMeasurable archimedeanRealGLBorel archimedeanComplexGLMeasurable
  archimedeanComplexGLBorel archimedeanRealNMeasurable archimedeanRealNBorel
  archimedeanComplexNMeasurable archimedeanComplexNBorel

/-- A nonzero entire normalization of a test yields an ordinary nonzero value
arbitrarily far to the right, away from the zeros of the L-denominator. -/
theorem OrdinaryIntegralNormalization.exists_ne_zero_above {Z : ℂ → ℂ}
    (L : ReciprocalEntire) (N : OrdinaryIntegralNormalization Z (fun s => (L.denominator s)⁻¹))
    {z : ℂ} (hz : N.value z ≠ 0) (a : ℝ) : ∃ s : ℂ, a < s.re ∧ Z s ≠ 0 := by
  obtain ⟨b, hb⟩ := N.eq_on_right
  have hv : ∀ᶠ s in codiscrete ℂ, N.value s ≠ 0 :=
    N.analytic.preimage_zero_mem_codiscrete hz
  have hL : ∀ᶠ s in codiscrete ℂ, L.denominator s ≠ 0 :=
    eventually_codiscrete_iff_forall_eventually_nhdsNE.mpr L.denominator_eventually_ne_zero
  have hU : IsOpen {s : ℂ | max a b < s.re} := isOpen_lt continuous_const Complex.continuous_re
  let p : ℂ := ↑(max a b + 1)
  have hp : p ∈ {s : ℂ | max a b < s.re} := by
    change max a b < (↑(max a b + 1) : ℂ).re
    simp only [Complex.ofReal_re]
    linarith
  have hfar : ∀ᶠ s in 𝓝[≠] p, max a b < s.re := nhdsWithin_le_nhds (hU.mem_nhds hp)
  obtain ⟨s, hs, hvs, hLs⟩ := (hfar.and ((hv.and hL).filter_mono (nhdsNE_le_codiscrete p))).exists
  refine ⟨s, (le_max_left a b).trans_lt hs, ?_⟩
  rw [hb s ((le_max_right a b).trans_lt hs)]
  exact mul_ne_zero hvs (inv_ne_zero hLs)

namespace UnequalOrdinaryPlaceReduction

/-- A meromorphic ordinary continuation, nonzero in the convergence half-plane,
forces a nonzero reflected dual value in that same half-plane. -/
private theorem pair_nonzero_of_equation {f g M Md A B : ℂ → ℂ} {σ : ℝ}
    (hf : DifferentiableOn ℂ f {s : ℂ | σ < s.re})
    (hg : DifferentiableOn ℂ g {s : ℂ | σ < s.re})
    (hM : MeromorphicOn M Set.univ)
    (hMf : ∀ s : ℂ, σ < s.re → f s = M s)
    (hMdg : ∀ s : ℂ, σ < s.re → g s = Md s)
    (heq : ∀ᶠ s in codiscrete ℂ, A s * Md (1 - s) = B s * M s)
    (hB : ∀ᶠ s in codiscrete ℂ, B s ≠ 0)
    (hn : ∃ z : ℂ, σ < z.re ∧ f z ≠ 0) :
    HolomorphicNonzeroOnRightHalfPlane f ∧ HolomorphicNonzeroOnRightHalfPlane g := by
  obtain ⟨z, hz, hne⟩ := hn
  have hm : DifferentiableOn ℂ M {s : ℂ | σ < s.re} :=
    hf.congr fun s hs => (hMf s hs).symm
  have hman : AnalyticAt ℂ M z :=
    hm.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re) z hz
  have hmn := EqualSemilocalReduction.eventually_ne_zero_of_analyticAt hM hman
    (by simpa only [← hMf z hz] using hne)
  have ho : IsOpen {s : ℂ | σ < (1 - s).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_const.sub continuous_id))
  let p : ℂ := 1 - ((σ + 1 : ℝ) : ℂ)
  have hp : p ∈ {s : ℂ | σ < (1 - s).re} := by simp [p]
  have hp' : ∀ᶠ s in 𝓝[≠] p, σ < (1 - s).re := nhdsWithin_le_nhds (ho.mem_nhds hp)
  obtain ⟨s, hs, he, hb, hm0⟩ :=
    (hp'.and ((heq.and (hB.and hmn)).filter_mono (nhdsNE_le_codiscrete p))).exists
  refine ⟨⟨σ, hf, z, hz, hne⟩, ⟨σ, hg, 1 - s, hs, ?_⟩⟩
  rw [hMdg (1 - s) hs]
  intro hzero
  exact mul_ne_zero hb hm0 (by simpa only [hzero, mul_zero] using he.symm)

private theorem reflected_multiplier_ne_zero (L : ReciprocalEntire) (c : ℂ)
    (hc : c ≠ 0) (ε : ℂ → ℂˣ) :
    ∀ᶠ s in codiscrete ℂ, c * (ε s : ℂ) * (L.denominator (1 - s))⁻¹ ≠ 0 := by
  let R : ReciprocalEntire := {
    denominator := fun s => L.denominator (1 - s)
    entire := L.entire.comp (show Differentiable ℂ (fun s : ℂ => 1 - s) by fun_prop)
    nonzero := by
      obtain ⟨z, hz⟩ := L.nonzero
      exact ⟨1 - z, by simpa only [sub_sub_cancel] using hz⟩ }
  have hn : ∀ᶠ s in codiscrete ℂ, R.denominator s ≠ 0 :=
    eventually_codiscrete_iff_forall_eventually_nhdsNE.mpr R.denominator_eventually_ne_zero
  filter_upwards [hn] with s hs
  exact mul_ne_zero (mul_ne_zero hc (ε s).ne_zero) (inv_ne_zero hs)

private theorem represented_scalar_ne_zero {G V : Type*} [Group G] [AddCommGroup V]
    [Module ℂ V] [Nontrivial V] (ρ : Representation ℂ G V) (k : G) :
    (if h : ∃ c : ℂ, ∀ x : V, ρ k x = c • x then h.choose else 1) ≠ 0 := by
  split_ifs with h
  · intro hc
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hzero : ρ k x = 0 := by rw [h.choose_spec x, hc, zero_smul]
    exact hx (by rw [← ρ.inv_self_apply k x, hzero, map_zero])
  · exact one_ne_zero

section Sign

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {n : ℕ}

local instance unequalTestRationalGroup : AddCommGroup (RationalInvariantFunctions F (n + 1)) :=
  Submodule.addCommGroup _
local instance unequalTestContinuousGroup : AddCommGroup (ContinuousRationalFunctions F (n + 1)) :=
  Submodule.addCommGroup _
local instance unequalTestFiniteGroup : AddCommGroup (FiniteSmoothRationalFunctions F (n + 1)) :=
  Submodule.addCommGroup _
local instance unequalTestFormsGroup : AddCommGroup (AutomorphicForms F (n + 1)) :=
  Submodule.addCommGroup _
local instance unequalTestStableGroup : AddCommGroup (StableAutomorphicFunctions F (n + 1)) :=
  Submodule.addCommGroup _
local instance unequalTestSpaceGroup (T : CuspidalOperatorRealization F n) : AddCommGroup T.Space :=
  Submodule.addCommGroup _

private theorem real_sign_ne_zero (T : CuspidalOperatorRealization F n)
    (v : {v : InfinitePlace F // v.IsReal}) : realMinusOneScalar T v ≠ 0 := by
  unfold realMinusOneScalar
  exact represented_scalar_ne_zero (T.realization.realPlaceCompactRepresentation v) (-1)

private theorem complex_sign_ne_zero (T : CuspidalOperatorRealization F n)
    (w : {w : InfinitePlace F // w.IsComplex}) : complexMinusOneScalar T w ≠ 0 := by
  unfold complexMinusOneScalar
  exact represented_scalar_ne_zero (T.realization.complexPlaceCompactRepresentation w) (-1)

end Sign

end UnequalOrdinaryPlaceReduction

open UnequalOrdinaryPlaceReduction

/-- Ordinary nonvanishing at a real place, on the actual restrictions used by the local
functional equation. No dual integral or choice of contragredient is needed as input. -/
def RealUnequalOrdinaryPlaceTestsStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r t : ℕ) (h : t < r) (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t)
    (v : {v : InfinitePlace F // v.IsReal}) (a : ℝˣ),
    IsRealAdditiveComponent ψ v.1 v.2 a →
  ∀ (d d' : List RealBlock),
    T.realization.HasRealPlaceParameter v d → T'.realization.HasRealPlaceParameter v d' →
    ∃ (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ)
      (D : RealQuotientMeasureData t),
      IsRealPlaceWhittaker F T ψ.complex v W ∧ IsRealPlaceWhittaker F T' ψ.complex⁻¹ v W' ∧
      ∀ σ : ℝ, ∃ s : ℂ, σ < s.re ∧ realUnequalIntegral h D W W' s ≠ 0

/-- Ordinary nonvanishing at a complex place on a single actual pair. -/
def ComplexUnequalOrdinaryPlaceTestsStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r t : ℕ) (h : t < r) (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t)
    (w : {w : InfinitePlace F // w.IsComplex}) (a : ℂˣ),
    IsComplexAdditiveComponent ψ w.1 w.2 a →
  ∀ (d d' : List ComplexCharacterData),
    T.realization.HasComplexPlaceParameter w d → T'.realization.HasComplexPlaceParameter w d' →
    ∃ (W : Langlands.GeneralLinear (r + 1) ℂ → ℂ) (W' : Langlands.GeneralLinear (t + 1) ℂ → ℂ)
      (D : ComplexQuotientMeasureData t),
      IsComplexPlaceWhittaker F T ψ.complex w W ∧ IsComplexPlaceWhittaker F T' ψ.complex⁻¹ w W' ∧
      ∀ σ : ℝ, ∃ s : ℂ, σ < s.re ∧ complexUnequalIntegral h D W W' s ≠ 0

/-- At one real place, the real local functional equation transfers ordinary nonvanishing
of a supplied actual pair to the dual integral, without changing the pair or its measure. -/
theorem hasRealUnequalPlaceTest_of_ordinary (hFE : RealUnequalFunctionalEquationStatement.{u})
    {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    {r t : ℕ} (h : t < r) (T Td : CuspidalOperatorRealization F r)
    (T' Td' : CuspidalOperatorRealization F t)
    (hTd : OperatorRealization.IsContragredientOf Td.realization T.realization)
    (hTd' : OperatorRealization.IsContragredientOf Td'.realization T'.realization)
    (v : {v : InfinitePlace F // v.IsReal}) (a : ℝˣ) (ha : IsRealAdditiveComponent ψ v.1 v.2 a)
    (d d' dd dd' : List RealBlock)
    (hd : T.realization.HasRealPlaceParameter v d) (hd' : T'.realization.HasRealPlaceParameter v d')
    (hdd : Td.realization.HasRealPlaceParameter v dd)
    (hdd' : Td'.realization.HasRealPlaceParameter v dd')
    (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ)
    (D : RealQuotientMeasureData t)
    (hW : IsRealPlaceWhittaker F T ψ.complex v W) (hW' : IsRealPlaceWhittaker F T' ψ.complex⁻¹ v W')
    (hn : ∀ σ : ℝ, ∃ s : ℂ, σ < s.re ∧ realUnequalIntegral h D W W' s ≠ 0) :
    HasRealUnequalPlaceTest h T T' ψ v a := by
  obtain ⟨σ, M, Md, -, -, hf, hg, hM, -, hm, hmd, heq⟩ :=
    hFE F ψ hψ r t h T Td T' Td' hTd hTd' v a ha d d' dd dd' hd hd' hdd hdd' D W W' hW hW'
  refine ⟨W, W', D, hW, hW', pair_nonzero_of_equation hf hg hM hm hmd heq ?_ (hn σ)⟩
  exact reflected_multiplier_ne_zero (realPairLFactor dd dd') _
    (pow_ne_zero r (real_sign_ne_zero T' v))
    (realPairEpsilon d d' a (NNReal.sqrt ‖(a : ℝ)‖₊)
      (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)))

/-- The same transfer at one complex place. -/
theorem hasComplexUnequalPlaceTest_of_ordinary (hFE : ComplexUnequalFunctionalEquationStatement.{u})
    {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    {r t : ℕ} (h : t < r) (T Td : CuspidalOperatorRealization F r)
    (T' Td' : CuspidalOperatorRealization F t)
    (hTd : OperatorRealization.IsContragredientOf Td.realization T.realization)
    (hTd' : OperatorRealization.IsContragredientOf Td'.realization T'.realization)
    (w : {w : InfinitePlace F // w.IsComplex}) (a : ℂˣ) (ha : IsComplexAdditiveComponent ψ w.1 w.2 a)
    (d d' dd dd' : List ComplexCharacterData)
    (hd : T.realization.HasComplexPlaceParameter w d)
    (hd' : T'.realization.HasComplexPlaceParameter w d')
    (hdd : Td.realization.HasComplexPlaceParameter w dd)
    (hdd' : Td'.realization.HasComplexPlaceParameter w dd')
    (W : Langlands.GeneralLinear (r + 1) ℂ → ℂ) (W' : Langlands.GeneralLinear (t + 1) ℂ → ℂ)
    (D : ComplexQuotientMeasureData t)
    (hW : IsComplexPlaceWhittaker F T ψ.complex w W)
    (hW' : IsComplexPlaceWhittaker F T' ψ.complex⁻¹ w W')
    (hn : ∀ σ : ℝ, ∃ s : ℂ, σ < s.re ∧ complexUnequalIntegral h D W W' s ≠ 0) :
    HasComplexUnequalPlaceTest h T T' ψ w a := by
  obtain ⟨σ, M, Md, -, -, hf, hg, hM, -, hm, hmd, heq⟩ :=
    hFE F ψ hψ r t h T Td T' Td' hTd hTd' w a ha d d' dd dd' hd hd' hdd hdd' D W W' hW hW'
  refine ⟨W, W', D, hW, hW', pair_nonzero_of_equation hf hg hM hm hmd heq ?_ (hn σ)⟩
  exact reflected_multiplier_ne_zero (complexPairLFactor dd dd') _
    (pow_ne_zero r (complex_sign_ne_zero T' w))
    (complexPairEpsilon d d' a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero))

/-- The real local functional equation transfers ordinary nonvanishing to the dual
without changing the chosen test functions or their measure. -/
theorem realUnequalPlaceTests_of_ordinary
    (hFE : RealUnequalFunctionalEquationStatement.{u})
    (hOrd : RealUnequalOrdinaryPlaceTestsStatement.{u}) : RealUnequalPlaceTestsStatement.{u} := by
  intro F _ _ _ ψ hψ r t h T Td T' Td' hTd hTd' v a ha d d' dd dd' hd hd' hdd hdd'
  obtain ⟨W, W', D, hW, hW', hn⟩ := hOrd F ψ hψ r t h T T' v a ha d d' hd hd'
  exact hasRealUnequalPlaceTest_of_ordinary hFE ψ hψ h T Td T' Td' hTd hTd' v a ha
    d d' dd dd' hd hd' hdd hdd' W W' D hW hW' hn

/-- The same deduction at a complex place. -/
theorem complexUnequalPlaceTests_of_ordinary
    (hFE : ComplexUnequalFunctionalEquationStatement.{u})
    (hOrd : ComplexUnequalOrdinaryPlaceTestsStatement.{u}) : ComplexUnequalPlaceTestsStatement.{u} := by
  intro F _ _ _ ψ hψ r t h T Td T' Td' hTd hTd' w a ha d d' dd dd' hd hd' hdd hdd'
  obtain ⟨W, W', D, hW, hW', hn⟩ := hOrd F ψ hψ r t h T T' w a ha d d' hd hd'
  exact hasComplexUnequalPlaceTest_of_ordinary hFE ψ hψ h T Td T' Td' hTd hTd' w a ha
    d d' dd dd' hd hd' hdd hdd' W W' D hW hW' hn

/-- The real and complex transfers are independent of one another. -/
def UnequalPlaceTestsFromOrdinaryStatement : Prop :=
  (RealUnequalFunctionalEquationStatement.{u} → RealUnequalOrdinaryPlaceTestsStatement.{u} →
    RealUnequalPlaceTestsStatement.{u}) ∧
  (ComplexUnequalFunctionalEquationStatement.{u} → ComplexUnequalOrdinaryPlaceTestsStatement.{u} →
    ComplexUnequalPlaceTestsStatement.{u})

theorem unequalPlaceTestsFromOrdinary : UnequalPlaceTestsFromOrdinaryStatement.{u} :=
  ⟨realUnequalPlaceTests_of_ordinary, complexUnequalPlaceTests_of_ordinary⟩

end Langlands.Global.RankinSelbergGlobal
