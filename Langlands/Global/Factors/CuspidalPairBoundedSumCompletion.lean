import Langlands.Global.Factors.CuspidalPairPoleEqualAssembly
import Langlands.Global.Factors.CuspidalPairPoleUnequalAssembly
import Langlands.Global.Factors.CuspidalPairPoleStripSums

/-! # Bounded completions from realized finite normalized sums -/

noncomputable section

set_option autoImplicit false

open NumberField Set

universe u uQ uI uJ

namespace Langlands.Global.CuspidalPairPoles

open RankinSelbergGlobal
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)
open RankinSelbergGlobal.UnequalAnalytic (unequalAnalyticStatement_proof)

local instance boundedSumSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance boundedSumSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

section Equal

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ} {T T' : CuspidalOperatorRealization F r}
  {P : CuspidalSpectralPresentation.{u, uQ} T} {P' : CuspidalSpectralPresentation.{u, uQ} T'}
  {h : HasIrreducibleAdmissibleComponents P} {h' : HasIrreducibleAdmissibleComponents P'}
  {c : FinitePairLChoice P P' h h'} {S : Finset (FinitePlace F)}
  {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}
  {ω ω' : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ} {Linf : ℂ → ℂ}

/-- An equal-rank normalized family with a bounded sum of realized tests gives a bounded
completion with the equal-test period pole criterion. -/
def EqualBoundedSumCompletionStatement
    (D : EqualNormalizedTests c S ψ Linf) : Prop :=
  (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  P.exceptional ⊆ S → P'.exceptional ⊆ S → FunctionalEquationComparison.FiniteAdditiveSupport ψ S →
  IsTrivialOnSplitCentre T → IsTrivialOnSplitCentre T' →
  T.realization.HasCentralCharacter ω → T'.realization.HasCentralCharacter ω' →
  (∃ σ : ℝ, ContinuousOn (fun s => Linf s * ∏' v, c.finiteL v s) {s | σ < s.re}) →
  ∀ {ι : Type uJ} (R : ι → ℂ → ℂ) (realize : ι → EqualPoleTest T T' S),
    (∀ i, D.normalized (realize i) = R i) → HasBoundedNormalizedSum R →
    ∃ Λ : ℂ → ℂ, c.IsCompletedLFunction Linf Λ ∧
      HasSimplePoleProfile Λ (HasEqualTestPeriod T T' S ω ω') ∧ IsBoundedInVerticalStrips Λ

theorem equalBoundedSumCompletion (D : EqualNormalizedTests c S ψ Linf) :
    EqualBoundedSumCompletionStatement (ω := ω) (ω' := ω') D := by
  intro hψ hPS hP'S hS hT hT' hω hω' hL ι R realize hreal hsum
  obtain ⟨Λ, hΛ, hp, hmatch⟩ := D.exists_completion hψ hPS hP'S hS hT hT' hω hω' hL
  choose I hI hEq using fun i => hmatch (realize i)
  refine ⟨Λ, hΛ, hp, isBoundedInVerticalStrips_of_bounded_normalized_sum I R Λ hsum ?_ hI⟩
  intro i s hs
  simpa only [hreal i] using hEq i s hs

end Equal

section Unequal

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r t : ℕ} {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
  {P : CuspidalSpectralPresentation.{u, uQ} T} {P' : CuspidalSpectralPresentation.{u, uQ} T'}
  {h : HasIrreducibleAdmissibleComponents P} {h' : HasIrreducibleAdmissibleComponents P'}
  {c : FinitePairLChoice P P' h h'} {hrt : t < r} {S : Finset (FinitePlace F)}
  {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)} {Linf : ℂ → ℂ}

/-- An unequal-rank normalized family with a bounded sum of realized tests gives a
completion bounded in strips, with removable singularities at `0` and `1`. -/
def UnequalBoundedSumCompletionStatement
    (D : UnequalNormalizedTests.{u, uQ, uI} c hrt S ψ Linf) : Prop :=
  (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  P.exceptional ⊆ S → P'.exceptional ⊆ S → FunctionalEquationComparison.FiniteAdditiveSupport ψ S →
  (∃ σ : ℝ, ContinuousOn (fun s => Linf s * ∏' v, c.finiteL v s) {s | σ < s.re}) →
  ∀ {ι : Type uJ} (R : ι → ℂ → ℂ) (realize : ι → D.Test),
    (∀ i, D.normalized (realize i) = R i) → HasBoundedNormalizedSum R →
    ∃ Λ : ℂ → ℂ, c.IsCompletedLFunction Linf Λ ∧
      HasSimplePoleProfile Λ False ∧ IsBoundedInVerticalStrips Λ

theorem unequalBoundedSumCompletion (D : UnequalNormalizedTests.{u, uQ, uI} c hrt S ψ Linf) :
    UnequalBoundedSumCompletionStatement D := by
  intro hψ hPS hP'S hS hL ι R realize hreal hsum
  obtain ⟨Λ, hΛ, hp, hmatch⟩ := D.exists_completion hψ hPS hP'S hS hL
  have hstd := isStandardAdditiveCharacter_of_unitary ψ hψ
  refine ⟨Λ, hΛ, hp, isBoundedInVerticalStrips_of_bounded_normalized_sum
    (D.integral ∘ realize) R Λ hsum ?_ ?_⟩
  · intro i s hs
    simpa only [Function.comp_apply, hreal i] using hmatch (realize i) s hs
  · intro i a b _ _
    by_cases hab : a ≤ b
    · obtain ⟨C, _, hC⟩ := (unequalAnalyticStatement_proof F r t hrt T T' ψ.complex hstd
        (D.left (realize i)) (D.right (realize i))).2.2.2.1 a b hab
      exact ⟨C, fun s ha hb _ _ => hC s ha hb⟩
    · exact ⟨0, fun _ ha hb _ _ => (hab (ha.trans hb)).elim⟩

end Unequal

end Langlands.Global.CuspidalPairPoles
