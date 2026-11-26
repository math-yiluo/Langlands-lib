import Langlands.Global.RankinSelberg.UnequalPlaceTestsFromOrdinary
import Langlands.Global.RankinSelberg.ComplexUnequalOrdinaryDescent
import Langlands.Global.RankinSelberg.ComplexUnequalTranslatedNormalization
import Langlands.Global.RankinSelberg.ComplexPlaceUnequalFunctionalEquationProof
import Langlands.Global.RankinSelberg.ComplexPlaceWhittakerRange
import Langlands.Global.RankinSelberg.ArchimedeanQuotientMeasures
import Langlands.Global.RankinSelberg.ArchimedeanWhittakerIdentityEvaluation

/-! # Ordinary nonvanishing at a complex place in unequal ranks -/

noncomputable section

open NumberField Filter Set
open scoped Classical CategoryTheory.MonObj Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.Global.RankinSelbergGlobal

open Automorphic HeckeFunctionalEquation ArchimedeanLocal LocalFactor.Archimedean
open ComplexUnequalTranslatedNormalization (complexUnequalTranslatedNormalization)
open ArchimedeanComplexPairFactor (complexLFactor_ne_zero)

attribute [local instance] archimedeanComplexGLMeasurable archimedeanComplexGLBorel
  archimedeanComplexNMeasurable archimedeanComplexNBorel archimedeanComplexQMeasurable
  archimedeanComplexQBorel

/-- Given a Whittaker intertwiner value nonzero at the identity and a smaller compact-finite
model coefficient nonzero at the identity, some larger compact-finite model coefficient has an
ordinary integral against the smaller one that is nonzero arbitrarily far to the right. -/
theorem exists_complexUnequalIntegral_ne_zero_above {r t : ℕ} (h : t < r)
    {d e : List ComplexCharacterData} (hd : d.length = r + 1) (he : e.length = t + 1)
    (a : ℂˣ) (D : ComplexQuotientMeasureData t)
    (B : Automorphic.complexStandardKFinite (r + 1) d →ₗ[ℂ] (Langlands.GeneralLinear (r + 1) ℂ → ℂ))
    (hB : IsComplexWhittakerIntertwiner r d a B) (v : Automorphic.complexStandardKFinite (r + 1) d)
    (V : complexWhittakerModel t e (-a)) (hv : B v 1 ≠ 0) (hV₁ : V.val 1 ≠ 0) :
    ∃ U : complexWhittakerModel r d a, ∀ b : ℝ, ∃ s : ℂ,
      b < s.re ∧ complexUnequalIntegral h D U.val V.val s ≠ 0 := by
  by_contra! hzero
  let W : complexWhittakerModel r d a :=
    ⟨B v, Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨v, rfl⟩)⟩
  have hvan (g₀ : Langlands.GeneralLinear (r + 1) ℂ) : ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      complexUnequalIntegral h D (ArchimedeanLocal.translateFunction g₀ W.val) V.val s = 0 := by
    obtain ⟨U, N, N₀, τ, hN, hRight, hLim, _, _, hRight₀⟩ :=
      complexUnequalTranslatedNormalization r t h d e a D
        (fun X Y => complexUnequalNormalizedGrowth r t h d e hd he a D X.val Y.val X.2 Y.2)
        B hB v g₀ V
    have hNzero (n : ℕ) : N n = 0 := by
      obtain ⟨p, hp⟩ := hzero (U n)
      ext z
      apply (show AnalyticOnNhd ℂ (N n) univ from fun s _ =>
        (hN n).analyticAt s).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (mem_univ (((max p τ + 1 : ℝ) : ℂ))) _ (mem_univ z)
      have hs : max p τ < (((max p τ + 1 : ℝ) : ℂ)).re := by simp
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with s hs'
      rw [hRight n s ((le_max_right _ _).trans_lt hs'), hp s ((le_max_left _ _).trans_lt hs'),
        mul_zero, Pi.zero_apply]
    have hN₀zero (z : ℂ) : N₀ z = 0 := by
      have ht := (hLim.tendstoLocallyUniformlyOn (s := Set.univ)).tendsto_at (mem_univ z)
      have ht₀ : Tendsto (fun n => N n z) atTop (𝓝 0) := by
        simp only [hNzero, Pi.zero_apply, tendsto_const_nhds]
      exact tendsto_nhds_unique ht ht₀
    obtain ⟨p, hp⟩ := complexLFactor_ne_zero (complexPairBlocks d e)
    refine ⟨max τ p, fun s hs => ?_⟩
    exact (mul_eq_zero.mp ((hRight₀ s ((le_max_left _ _).trans_lt hs)).symm.trans
      (hN₀zero s))).resolve_left (hp s ((le_max_right _ _).trans_lt hs))
  have hzero₁ := ComplexUnequalOrdinaryDescent.eq_zero_of_translates_vanish
    (ComplexUnequalOrdinaryDescent.isGood_of_mem_model W.2) t h D V.val
    (ComplexUnequalOrdinaryDescent.isGood_of_mem_model V.2) hvan
  exact mul_ne_zero hv hV₁ hzero₁

/-- **Ordinary nonvanishing at a complex place.** For every unequal-rank pair of actual
cuspidal realizations, an actual pair of complex-place Whittaker restrictions and a compatible
quotient measure give an ordinary local integral with a nonzero value in every right
half-plane. -/
theorem complexUnequalOrdinaryPlaceTests : ComplexUnequalOrdinaryPlaceTestsStatement.{u} := by
  intro F _ _ _ ψ hψ r t h T T' w a ha d e hd he
  obtain ⟨_, B, _, hB, ⟨v, hv⟩, _⟩ :=
    (archimedeanActualWhittakerIntertwiners F ψ hψ r T).2 w d hd a ha
  have hχ := UnramifiedWhittaker.isStandardAdditiveCharacter_complex F ψ hψ
  have hχ' := Unfolding.isStandardAdditiveCharacter_inv F ψ.complex hχ
  obtain ⟨V, hV, hV₁⟩ :=
    ArchimedeanWhittakerEvaluation.exists_complexPlaceWhittaker_one_ne_zero T' ψ.complex⁻¹ hχ' w
  let V' : complexWhittakerModel t e (-a) :=
    ⟨V, ((complexPlaceWhittakerModelReduction
      (complexPlaceWhittakerIntertwinerReduction complexPlaceWhittakerAnalytic))
        F ψ hψ t T' w a ha e he V).2 hV⟩
  let D := complexQuotientMeasureData t
  obtain ⟨U, hU⟩ := exists_complexUnequalIntegral_ne_zero_above h hd.1 he.1 a D B hB v V'
    (by rw [hv]; exact one_ne_zero) hV₁
  obtain ⟨x, hx⟩ := complexPlaceWhittakerRange F ψ hψ r T w d hd a ha U.val U.2
  refine ⟨U.val, V, D, ⟨x, 1, ?_⟩, hV, hU⟩
  funext g
  simpa only [finitePoint, map_one, ArchimedeanWhittakerEvaluation.adelicPoint_one, mul_one]
    using hx g

end Langlands.Global.RankinSelbergGlobal
