import Langlands.Global.Factors.CuspidalPairPolePureSpan
import Langlands.Global.RankinSelberg.EqualEulerFactorizationProof

/-! # Extending ordinary equal-rank normalizations to the spans of pure vectors -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

universe u uQ

open NumberField MeasureTheory Set
open scoped Classical CategoryTheory.MonObj

namespace Langlands.Global.CuspidalPairPoles

open Automorphic RankinSelbergGlobal InfinitePlaceFamily
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)

private theorem normalization_of_right_add {I J K L : ℂ → ℂ} {a : ℝ}
    (h : ∀ s, a < s.re → I s = J s + K s)
    (hJ : Nonempty (OrdinaryIntegralNormalization J L)) (hK : Nonempty (OrdinaryIntegralNormalization K L)) :
    Nonempty (OrdinaryIntegralNormalization I L) := by
  obtain ⟨NJ⟩ := hJ
  obtain ⟨NK⟩ := hK
  obtain ⟨b, hb⟩ := NJ.eq_on_right
  obtain ⟨c, hc⟩ := NK.eq_on_right
  refine ⟨⟨fun s => NJ.value s + NK.value s, fun s hs => (NJ.analytic s hs).fun_add (NK.analytic s hs),
    max a (max b c), fun s hs => ?_⟩⟩
  have hbc := (le_max_right a (max b c)).trans_lt hs
  rw [h s ((le_max_left _ _).trans_lt hs), hb s ((le_max_left _ _).trans_lt hbc),
    hc s ((le_max_right _ _).trans_lt hbc), add_mul]

private theorem normalization_of_right_smul {I J L : ℂ → ℂ} {a : ℝ} (c : ℂ)
    (h : ∀ s, a < s.re → I s = c * J s) (hJ : Nonempty (OrdinaryIntegralNormalization J L)) :
    Nonempty (OrdinaryIntegralNormalization I L) := by
  obtain ⟨N⟩ := hJ
  obtain ⟨b, hb⟩ := N.eq_on_right
  refine ⟨⟨fun s => c * N.value s, fun s hs => analyticAt_const.fun_mul (N.analytic s hs),
    max a b, fun s hs => ?_⟩⟩
  rw [h s ((le_max_left a b).trans_lt hs), hb s ((le_max_right a b).trans_lt hs), mul_assoc]

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ} {T T' : CuspidalOperatorRealization F r}
  {P : CuspidalSpectralPresentation.{u, uQ} T} {P' : CuspidalSpectralPresentation.{u, uQ} T'}
  {hP : HasIrreducibleAdmissibleComponents P} {hP' : HasIrreducibleAdmissibleComponents P'}
  {S : Finset (FinitePlace F)}
  {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}

local instance poleSpanNormalizationAffine (n : ℕ) : AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance poleSpanNormalizationSmooth (n : ℕ) : AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _
local instance poleSpanNormalizationRationalGroup (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance poleSpanNormalizationContinuousGroup (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance poleSpanNormalizationFiniteSmoothGroup (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance poleSpanNormalizationAutomorphicGroup (n : ℕ) : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance poleSpanNormalizationStableGroup (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance poleSpanNormalizationSpaceGroup (T₀ : CuspidalOperatorRealization F r) :
    AddCommGroup T₀.Space := Submodule.addCommGroup _

/-- Existence of ordinary normalizations at a fixed Schwartz test on both pure-vector spans. -/
def HasOrdinaryEqualNormalizationsOnPureSpans (c : FinitePairLChoice P P' hP hP')
    (hPS : P.exceptional ⊆ S) (hPS' : P'.exceptional ⊆ S)
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)) (Φ : RowVector F (r + 1) → ℂ)
    (Linf : ℂ → ℂ) : Prop :=
  ∀ (x : T.Space) (x' : T'.Space),
    x ∈ poleEqualPureSpan P hP hPS → x' ∈ poleEqualPureSpan P' hP' hPS' →
    Nonempty (OrdinaryIntegralNormalization
      (partialEqualWhittakerIntegral F S (cuspWhittaker F T ψ.complex x) (cuspWhittaker F T' ψ.complex⁻¹ x') Φ)
      (fun s => Linf s * ∏ v ∈ S, c.finiteL v s))

/-- Normalizations at every pure pair extend along both spans for a fixed Schwartz test
standard outside the retained set. Absolute convergence supplies linearity on the right. -/
theorem hasOrdinaryEqualNormalizationsOnPureSpans (c : FinitePairLChoice P P' hP hP')
    (hPS : P.exceptional ⊆ S) (hPS' : P'.exceptional ⊆ S)
    (hψF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (hS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    (Φ : RowVector F (r + 1) → ℂ) (hΦ : Φ ∈ schwartzBruhat F (r + 1))
    (hΦstd : IsStandardOutside F (r + 1) S Φ) (Linf : ℂ → ℂ)
    (hPure : ∀ (a : ∀ v : S, P.localFactor v) (a' : ∀ v : S, P'.localFactor v)
      (b : ∀ i : Index F, T.placeDensityModels.subspace i)
      (b' : ∀ i : Index F, T'.placeDensityModels.subspace i),
      Nonempty (OrdinaryIntegralNormalization
        (partialEqualWhittakerIntegral F S
          (cuspWhittaker F T ψ.complex (poleEqualPureVector P hP hPS a b))
          (cuspWhittaker F T' ψ.complex⁻¹ (poleEqualPureVector P' hP' hPS' a' b')) Φ)
        (fun s => Linf s * ∏ v ∈ S, c.finiteL v s))) :
    HasOrdinaryEqualNormalizationsOnPureSpans c hPS hPS' ψ Φ Linf := by
  let L (s : ℂ) := Linf s * ∏ v ∈ S, c.finiteL v s
  let I (x : T.Space) (y : T'.Space) :=
    partialEqualWhittakerIntegral F S (cuspWhittaker F T ψ.complex x) (cuspWhittaker F T' ψ.complex⁻¹ y) Φ
  let μS := (whittakerQuotientMeasure F (r + 1)).restrict (unipotentIntegralClasses F (r + 1) S)
  let M := poleEqualPureSpan P hP hPS
  let N := poleEqualPureSpan P' hP' hPS'
  have hχ := UnramifiedWhittaker.isStandardAdditiveCharacter_complex F ψ hψF
  have hχ' := Unfolding.isStandardAdditiveCharacter_inv F ψ.complex hχ
  let W (q : WhittakerQuotient F (r + 1)) := UnramifiedWhittaker.whittakerFunctional F ψ.complex hχ T q.out
  let W' (q : WhittakerQuotient F (r + 1)) := UnramifiedWhittaker.whittakerFunctional F ψ.complex⁻¹ hχ' T' q.out
  let K (s : ℂ) (q : WhittakerQuotient F (r + 1)) : T.Space →ₗ[ℂ] T'.Space →ₗ[ℂ] ℂ :=
    LinearMap.mk₂ ℂ (fun x y => (W q x * W' q y) * Φ (lastRow F r q.out) * detPower F (r + 1) q.out s)
      (fun x y z => by simp only [map_add, add_mul])
      (fun c x y => by simp only [map_smul, smul_eq_mul, mul_assoc])
      (fun x y z => by simp only [map_add, mul_add, add_mul])
      (fun c x y => by simp only [map_smul, smul_eq_mul]; ring)
  obtain ⟨σ, hσ⟩ := equalEulerFactorization F ψ hψF r T T' P P' S hPS hPS' hS
  have hInt (s : ℂ) (hs : σ < s.re) (x : T.Space) (y : T'.Space) (hx : x ∈ M) (hy : y ∈ N) :
      Integrable (fun q => K s q x y) μS :=
    ((hσ x y Φ (sphericalOutside_of_mem_poleEqualPureSpan P hP hPS hx)
      (sphericalOutside_of_mem_poleEqualPureSpan P' hP' hPS' hy) hΦ hΦstd s hs).1).integrableOn
  have hI (x y s) : I x y s = ∫ q, K s q x y ∂μS := rfl
  intro x y hx hy
  change Nonempty (OrdinaryIntegralNormalization (I x y) L)
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
      obtain ⟨a, b, rfl⟩ := hx
      obtain ⟨a', b', rfl⟩ := hy
      exact hPure a a' b b'
  | zero_left y hy =>
      exact ⟨⟨0, fun s _ => analyticAt_const, 0, fun s _ => by simp [hI]⟩⟩
  | zero_right x hx =>
      exact ⟨⟨0, fun s _ => analyticAt_const, 0, fun s _ => by simp [hI]⟩⟩
  | add_left x z y hx hz hy h₁ h₂ =>
      apply normalization_of_right_add (a := σ) _ h₁ h₂
      intro s hs
      simp only [hI, map_add, LinearMap.add_apply]
      exact integral_add (hInt s hs x y hx hy) (hInt s hs z y hz hy)
  | add_right x y z hx hy hz h₁ h₂ =>
      apply normalization_of_right_add (a := σ) _ h₁ h₂
      intro s hs
      simp only [hI, map_add]
      exact integral_add (hInt s hs x y hx hy) (hInt s hs x z hx hz)
  | smul_left c x y hx hy h =>
      apply normalization_of_right_smul (a := σ) c _ h
      intro s _
      simp only [hI, map_smul, LinearMap.smul_apply, smul_eq_mul, integral_const_mul]
  | smul_right c x y hx hy h =>
      apply normalization_of_right_smul (a := σ) c _ h
      intro s _
      simp only [hI, map_smul, smul_eq_mul, integral_const_mul]

end Langlands.Global.CuspidalPairPoles
