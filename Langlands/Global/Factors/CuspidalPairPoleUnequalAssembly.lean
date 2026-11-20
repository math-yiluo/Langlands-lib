import Langlands.Global.Factors.CuspidalPairPoleContinuation
import Langlands.Global.Factors.CuspidalPairPoleFiniteEuler
import Langlands.Global.RankinSelberg.UnequalAnalyticProof
import Langlands.Global.RankinSelberg.UnequalEulerFactorizationProof
import Langlands.Global.RankinSelberg.EqualDualEulerFactorizationReduction

/-! # Unequal-rank assembly from normalized partial integrals -/

noncomputable section

set_option autoImplicit false

universe u uQ uI

namespace Langlands.Global.CuspidalPairPoles

open NumberField RankinSelbergGlobal
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)
open RankinSelbergGlobal.UnequalAnalytic (unequalAnalyticStatement_proof)

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r t : ℕ} {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
  {P : CuspidalSpectralPresentation.{u, uQ} T} {P' : CuspidalSpectralPresentation.{u, uQ} T'}
  {h : HasIrreducibleAdmissibleComponents P} {h' : HasIrreducibleAdmissibleComponents P'}
  {c : FinitePairLChoice P P' h h'} {hrt : t < r} {S : Finset (FinitePlace F)}
  {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)} {Linf : ℂ → ℂ}

/-- Whole-plane normalized values of partial unequal-rank integrals for a family
of actual cuspidal vectors. The normalization uses the selected factors at `S`
and the archimedean function `Linf`. -/
structure UnequalNormalizedTests (c : FinitePairLChoice P P' h h') (hrt : t < r)
    (S : Finset (FinitePlace F)) (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (Linf : ℂ → ℂ) where
  Test : Type uI
  left : Test → T.Space
  right : Test → T'.Space
  sphericalLeft : ∀ i, IsSphericalOutside F T S (left i)
  sphericalRight : ∀ i, IsSphericalOutside F T' S (right i)
  normalized : Test → ℂ → ℂ
  analytic : ∀ i, AnalyticOnNhd ℂ (normalized i) Set.univ
  nonvanishing : ∀ s, ∃ i, normalized i s ≠ 0
  partial_eq : ∀ i, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
    partialUnequalWhittakerIntegral F hrt S
      (cuspWhittaker F T ψ.complex (left i)) (cuspWhittaker F T' ψ.complex⁻¹ (right i)) s =
        normalized i s * Linf s * ∏ v ∈ S, c.finiteL v s

namespace UnequalNormalizedTests

variable (D : UnequalNormalizedTests.{u, uQ, uI} c hrt S ψ Linf)

/-- The ordinary global integral of one member of the test family. -/
def integral (i : D.Test) : ℂ → ℂ :=
  unequalIntegral F hrt ψ.complex (cuspFunction F T (D.left i)) (cuspFunction F T' (D.right i))

/-- Unfolding and partial Euler factorization match each test to the full finite
Euler product multiplied by the prescribed archimedean factor. -/
theorem integral_eq_on_right (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
    (hS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S) :
    ∀ i, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      D.integral i s = D.normalized i s * (Linf s * ∏' v, c.finiteL v s) := by
  have hstd := isStandardAdditiveCharacter_of_unitary ψ hψ
  obtain ⟨σU, _, hU⟩ := unequalUnfoldingStatement_proof F r t hrt T T'
  obtain ⟨σE, hE⟩ := unequalEulerFactorization F ψ hψ r t hrt T T' P P' S hP hP' hS
  obtain ⟨σL, hL⟩ := c.exists_finiteL_convergence hP hP'
  intro i
  obtain ⟨σD, hD⟩ := D.partial_eq i
  refine ⟨max (max σU σE) (max σL σD), fun s hs => ?_⟩
  have hσU := lt_of_le_of_lt (le_max_left σU σE) (lt_of_le_of_lt (le_max_left _ _) hs)
  have hσE := lt_of_le_of_lt (le_max_right σU σE) (lt_of_le_of_lt (le_max_left _ _) hs)
  have hσL := lt_of_le_of_lt (le_max_left σL σD) (lt_of_le_of_lt (le_max_right _ _) hs)
  have hσD := lt_of_le_of_lt (le_max_right σL σD) (lt_of_le_of_lt (le_max_right _ _) hs)
  have hUeq := ((hU ψ.complex hstd (D.left i) (D.right i)).1 s hσU).2
  obtain ⟨_, _, p, hp, hfact⟩ := hE (D.left i) (D.right i)
    (D.sphericalLeft i) (D.sphericalRight i) s hσE
  have hp' : partialEulerProduct P P' hP hP' s = p := hp.tprod_eq
  have hfull := (hL s hσL).2.tprod_eq
  unfold integral
  rw [hUeq, hfact, ← hp', hD s hσD, hfull]
  ring

/-- A covering normalized family gives a completed function with no poles in
unequal rank. Only matching and pointwise nonvanishing of the normalized test
family are needed from the ramified and archimedean factor analysis here. -/
theorem exists_completion (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
    (hS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    (hL : ∃ σ : ℝ, ContinuousOn (fun s => Linf s * ∏' v, c.finiteL v s) {s | σ < s.re}) :
    ∃ Λ : ℂ → ℂ, c.IsCompletedLFunction Linf Λ ∧ HasSimplePoleProfile Λ False ∧
      ∀ i s, s ∉ ({0, 1} : Set ℂ) → D.integral i s = D.normalized i s * Λ s := by
  have hstd := isStandardAdditiveCharacter_of_unitary ψ hψ
  have hanalytic (i : D.Test) : Differentiable ℂ (D.integral i) :=
    (unequalAnalyticStatement_proof F r t hrt T T' ψ.complex hstd
      (D.left i) (D.right i)).2.2.1
  have hNoPole (p : ℂ) : (∃ i, meromorphicOrderAt (D.integral i) p < 0) ↔ False :=
    ⟨fun ⟨i, hi⟩ => (not_lt_of_ge ((hanalytic i).analyticAt p).meromorphicOrderAt_nonneg) hi,
      False.elim⟩
  have hlower : (-1 : WithTop ℤ) ≤ 0 :=
    WithTop.coe_le_coe.mpr (by norm_num : (-1 : ℤ) ≤ 0)
  obtain ⟨Λ, ⟨a, ha⟩, hagree, hpoles⟩ := exists_continuation_of_normalized_tests
    D.integral D.normalized (fun s => Linf s * ∏' v, c.finiteL v s) False
    (fun i => (hanalytic i).differentiableOn)
    (fun i p _ => ⟨((hanalytic i).analyticAt p).meromorphicAt,
      hlower.trans ((hanalytic i).analyticAt p).meromorphicOrderAt_nonneg⟩)
    D.analytic D.nonvanishing hL (D.integral_eq_on_right hψ hP hP' hS) (fun p _ => hNoPole p)
  obtain ⟨b, hb⟩ := c.exists_finiteL_convergence hP hP'
  refine ⟨Λ, ⟨max a b, fun s hs => ?_⟩, hpoles, hagree⟩
  obtain ⟨hsum, hprod⟩ := hb s (lt_of_le_of_lt (le_max_right a b) hs)
  exact ⟨hsum, _, hprod.multipliable.hasProd, ha s (lt_of_le_of_lt (le_max_left a b) hs)⟩

/-- A finite identity among normalized tests equal to one proves strip bounds for
the resulting completion by the global unequal-rank integral estimates. -/
theorem completion_bounded_of_normalized_sum
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) {Λ : ℂ → ℂ}
    (hΛ : ∀ i s, s ∉ ({0, 1} : Set ℂ) → D.integral i s = D.normalized i s * Λ s)
    (A : Finset D.Test) (a : D.Test → ℂ)
    (hA : ∀ s ∉ ({0, 1} : Set ℂ), ∑ i ∈ A, a i * D.normalized i s = 1) :
    IsBoundedInVerticalStrips Λ := by
  have hstd := isStandardAdditiveCharacter_of_unitary ψ hψ
  refine isBoundedInVerticalStrips_of_normalized_sum D.integral D.normalized Λ A a
    (fun i _ => hΛ i) hA (fun i _ x y ε _ => ?_)
  by_cases hxy : x ≤ y
  · obtain ⟨C, _, hC⟩ := (unequalAnalyticStatement_proof F r t hrt T T' ψ.complex hstd
      (D.left i) (D.right i)).2.2.2.1 x y hxy
    exact ⟨C, fun s hx hy _ _ => hC s hx hy⟩
  · exact ⟨0, fun s hx hy _ _ => (hxy (hx.trans hy)).elim⟩

end UnequalNormalizedTests

end Langlands.Global.CuspidalPairPoles
