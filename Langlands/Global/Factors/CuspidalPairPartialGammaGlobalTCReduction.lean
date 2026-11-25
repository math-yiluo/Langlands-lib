import Langlands.Global.Factors.CuspidalPairPartialGammaGlobalReduction
import Langlands.Global.Factors.CuspidalPairPartialGammaEquationTCStatement
import Langlands.Global.RankinSelberg.SemilocalEquationTCStatements

/-!
# The totally complex partial equation of cuspidal pairs from the global Rankin–Selberg theory

The totally complex form of `cuspidalPairPartialGammaGlobalReduction`: the eight premises
of `CuspidalPairPartialGammaGlobalReductionStatement` that involve no archimedean local
factors, unrestricted, and the totally complex forms of the two semi-local equations imply
`CuspidalPairPartialGammaEquationTCStatement`. See the paired Markdown.
-/

noncomputable section

set_option autoImplicit false

universe u uQ

namespace Langlands.Global

open NumberField HeckeFunctionalEquation CuspidalPairFunctionalEquation
open CuspidalPairBoundaryNonvanishing
open LocalFactor.Archimedean
open Langlands.Global.CompletionPadic Langlands.ClassFieldTheory.Global.RelativeWeilGroup
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation OperatorRealization)
open Filter
open scoped _root_.Topology

namespace CuspidalPairPartialGammaTC

open CuspidalPairPartialGammaGlobal

/-! ### The unrestricted statements imply their totally complex forms -/

/-- The unrestricted unequal-rank semi-local equation implies its totally complex form. -/
theorem unequalSemilocalEquationTC_of_unrestricted
    (h : RankinSelbergGlobal.UnequalSemilocalEquationStatement.{u, uQ}) :
    RankinSelbergGlobal.UnequalSemilocalEquationTCStatement.{u, uQ} :=
  fun F _ _ _ _ => h F

/-- The unrestricted equal-rank semi-local equation implies its totally complex form. -/
theorem equalSemilocalEquationTC_of_unrestricted
    (h : RankinSelbergGlobal.EqualSemilocalEquationStatement.{u, uQ}) :
    RankinSelbergGlobal.EqualSemilocalEquationTCStatement.{u, uQ} :=
  fun F _ _ _ _ => h F

/-- The unrestricted partial equation (G') implies its totally complex form. -/
theorem cuspidalPairPartialGammaEquationTC_of_unrestricted
    (h : CuspidalPairPartialGammaEquationStatement.{u, uQ}) :
    CuspidalPairPartialGammaEquationTCStatement.{u, uQ} :=
  fun F _ _ _ _ => h F

/-! ### The totally complex packages -/

/-- The totally complex form of `UnequalPackageStatement`. What the four unrestricted
unequal-rank premises and the totally complex semi-local equation give for `t < r` over a
totally complex field: meromorphic continuations `I`,
`J` of the global integral and of its dual with `I(s) = J(1 - s)`, meromorphic semi-local
factors `A`, `B`, nonzero off a discrete set, the partial Euler factorizations
`I = A ∏_(v ∉ S) L_v`, `J = B ∏_(v ∉ S) L∨_v` on a right half-plane, and the semi-local
equation `L_∞(s) B(1 - s) = (∏_(v ∈ S) γ_v(s)) ε_∞(s) L∨_∞(1 - s) A(s)`. -/
def UnequalPackageTCStatement : Prop := by
  classical
  exact
  ∀ (F : Type u) [Field F] [NumberField F]
    [NumberField.IsTotallyComplex F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (diagonal F x) = 1) →
  ∀ (r t : ℕ) (_h : t < r) (T Td : CuspidalOperatorRealization F r)
    (T' Td' : CuspidalOperatorRealization F t),
    OperatorRealization.IsContragredientOf Td.realization T.realization →
    OperatorRealization.IsContragredientOf Td'.realization T'.realization →
  ∀ (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (Pd : CuspidalSpectralPresentation.{u, uQ} Td)
    (Pd' : CuspidalSpectralPresentation.{u, uQ} Td')
    (h : HasIrreducibleAdmissibleComponents P) (h' : HasIrreducibleAdmissibleComponents P')
    (S : Finset (FinitePlace F)) (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
    (hPd : Pd.exceptional ⊆ S) (hPd' : Pd'.exceptional ⊆ S),
    FunctionalEquationComparison.FiniteAdditiveSupport ψ S →
  ∀ (aR : {v : InfinitePlace F // v.IsReal} → ℝˣ),
    (∀ v, IsRealAdditiveComponent ψ v.1 v.2 (aR v)) →
  ∀ (aC : {v : InfinitePlace F // v.IsComplex} → ℂˣ),
    (∀ v, IsComplexAdditiveComponent ψ v.1 v.2 (aC v)) →
  ∀ (dR dR' dRd dRd' : {v : InfinitePlace F // v.IsReal} → List RealBlock),
    (∀ v, OperatorRealization.HasRealPlaceParameter T.realization v (dR v)) →
    (∀ v, OperatorRealization.HasRealPlaceParameter T'.realization v (dR' v)) →
    (∀ v, OperatorRealization.HasRealPlaceParameter Td.realization v (dRd v)) →
    (∀ v, OperatorRealization.HasRealPlaceParameter Td'.realization v (dRd' v)) →
  ∀ (dC dC' dCd dCd' : {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData),
    (∀ v, OperatorRealization.HasComplexPlaceParameter T.realization v (dC v)) →
    (∀ v, OperatorRealization.HasComplexPlaceParameter T'.realization v (dC' v)) →
    (∀ v, OperatorRealization.HasComplexPlaceParameter Td.realization v (dCd v)) →
    (∀ v, OperatorRealization.HasComplexPlaceParameter Td'.realization v (dCd' v)) →
  let infiniteL (s : ℂ) : ℂ :=
    (∏ v, ((realPairLFactor (dR v) (dR' v)).denominator s)⁻¹) *
      ∏ v, ((complexPairLFactor (dC v) (dC' v)).denominator s)⁻¹
  let dualInfiniteL (s : ℂ) : ℂ :=
    (∏ v, ((realPairLFactor (dRd v) (dRd' v)).denominator s)⁻¹) *
      ∏ v, ((complexPairLFactor (dCd v) (dCd' v)).denominator s)⁻¹
  let infiniteEpsilon (s : ℂ) : ℂ :=
    (∏ v, (realPairEpsilon (dR v) (dR' v) (aR v) (NNReal.sqrt ‖((aR v : ℝ))‖₊)
        (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr (aR v).ne_zero)) s : ℂ)) *
      ∏ v, (complexPairEpsilon (dC v) (dC' v) (aC v) ‖((aC v : ℂ))‖₊
        (nnnorm_pos.mpr (aC v).ne_zero) s : ℂ)
  ∃ (σ : ℝ) (I J A B : ℂ → ℂ),
    MeromorphicOn I Set.univ ∧ MeromorphicOn J Set.univ ∧
    MeromorphicOn A Set.univ ∧ MeromorphicOn B Set.univ ∧
    (∀ᶠ s in codiscrete ℂ, A s ≠ 0) ∧ (∀ᶠ s in codiscrete ℂ, B s ≠ 0) ∧
    (∀ᶠ s in codiscrete ℂ, I s = J (1 - s)) ∧
    (∀ s : ℂ, σ < s.re → ∃ p : ℂ,
      HasProd (fun v => partialEulerFactor P P' hP hP' v s) p ∧ I s = A s * p) ∧
    (∀ s : ℂ, σ < s.re → ∃ p : ℂ,
      HasProd (fun v => partialEulerFactor Pd Pd' hPd hPd' v s) p ∧ J s = B s * p) ∧
    ∀ (ψv : ∀ v : FinitePlace F, Correspondence.NontrivialAdditiveCharacter (padicField v)),
      (∀ v, IsCanonicalFiniteAdditiveComponent ψ v (ψv v)) →
    ∀ (νv : ∀ v : FinitePlace F, Correspondence.LocalAdditiveHaarMeasure (padicField v)),
      (∀ v, Correspondence.IsSelfDualMeasure (padicField v) (ψv v) (νv v)) →
    ∀ G : FinitePlace F → RankinSelberg.RationalFunctions,
      (∀ v ∈ S,
        letI := (padicField v).canonicalTopologicalData.topology
        letI := (padicField v).canonicalGeneralLinearTopology (r + 1)
        letI := (padicField v).canonicalGeneralLinearTopology (t + 1)
        RankinSelberg.IsPadicSymmetricGammaFactor (padicField v) (ψv v) (νv v)
          ((P.localComponent v).padicObject (h v).1 (h v).2).obj.representation
          ((P'.localComponent v).padicObject (h' v).1 (h' v).2).obj.representation (G v)) →
    ∀ᶠ s in codiscrete ℂ,
      infiniteL s * B (1 - s) =
        (∏ v ∈ S, RatFunc.eval (RingHom.id ℂ)
          (RankinSelberg.spectralPoint (residueCardinality v) s) (G v)) *
          infiniteEpsilon s * dualInfiniteL (1 - s) * A s

/-- The four unrestricted unequal-rank premises and the totally complex semi-local equation
give the totally complex unequal-rank package. -/
theorem unequalPackageTC (hA : RankinSelbergGlobal.UnequalAnalyticStatement.{u})
    (hU : RankinSelbergGlobal.UnequalUnfoldingStatement.{u})
    (hE : RankinSelbergGlobal.UnequalEulerFactorizationStatement.{u, uQ})
    (hD : RankinSelbergGlobal.UnequalDualEulerFactorizationStatement.{u, uQ})
    (hS : RankinSelbergGlobal.UnequalSemilocalEquationTCStatement.{u, uQ}) :
    UnequalPackageTCStatement.{u, uQ} := by
  intro F _ _ _ _ ψ hdiag r t hrt T Td T' Td' hTd hTd' P P' Pd Pd' h h' S hP hP' hPd hPd'
    hsupp aR haR aC haC dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd
    hdCd'
  have hstd := isStandardAdditiveCharacter_complex ψ hdiag
  obtain ⟨x, x', hx, hx', σS, A, B, hAm, hBm, hAeq, hBeq, hA0, hB0, hsem⟩ :=
    hS F ψ hdiag r t hrt T Td T' Td' hTd hTd' P P' h h' S hP hP' hsupp aR haR aC haC
      dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd hdCd'
  obtain ⟨C, -, hC⟩ := hU F r t hrt T T'
  obtain ⟨σE, hσE⟩ := hE F ψ hdiag r t hrt T T' P P' S hP hP' hsupp
  obtain ⟨σD, hσD⟩ := hD F ψ hdiag r t hrt T Td T' Td' hTd hTd' Pd Pd' S hPd hPd' hsupp
  obtain ⟨-, -, hIdiff, -, hIdual⟩ := hA F r t hrt T T' ψ.complex hstd x x'
  obtain ⟨hU1, hU2⟩ := hC ψ.complex hstd x x'
  let I : ℂ → ℂ := RankinSelbergGlobal.unequalIntegral F hrt ψ.complex
    (RankinSelbergGlobal.cuspFunction F T x) (RankinSelbergGlobal.cuspFunction F T' x')
  have hIdiff' : Differentiable ℂ I := hIdiff
  refine ⟨max (max C σE) (max (1 + C) (max σD σS)), I, fun u => I (1 - u), A, B,
    fun z _ => (hIdiff'.analyticAt z).meromorphicAt,
    fun z _ => ((hIdiff'.comp ((differentiable_const 1).sub differentiable_id)).analyticAt
      z).meromorphicAt,
    hAm, hBm, hA0, hB0, Eventually.of_forall fun s => by simp only [sub_sub_cancel],
    ?_, ?_, hsem⟩
  · intro s hσ
    simp only [max_lt_iff] at hσ
    obtain ⟨⟨hCs, hEs⟩, -, -, hSs⟩ := hσ
    obtain ⟨-, -, p, hp, hWp⟩ := hσE x x' hx hx' s hEs
    refine ⟨p, hp, ?_⟩
    rw [hAeq s hSs]
    exact (hU1 s hCs).2.trans hWp
  · intro u hσ
    simp only [max_lt_iff] at hσ
    obtain ⟨-, h1C, hDu, hSu⟩ := hσ
    obtain ⟨-, -, p, hp, hWp⟩ := hσD x x' hx hx' u hDu
    refine ⟨p, hp, ?_⟩
    have hu1 : (1 - u).re < -C := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have e1 := hIdual (1 - u)
    have e2 := (hU2 (1 - u) hu1).2
    rw [sub_sub_cancel] at e1 e2
    rw [hBeq u hSu]
    exact e1.trans (e2.trans hWp)

/-- The totally complex form of `EqualPackageStatement`. What the four unrestricted
equal-rank premises and the totally complex semi-local equation give for `t = r` over a
totally complex field, in the form of
`UnequalPackageTCStatement`. -/
def EqualPackageTCStatement : Prop := by
  classical
  exact
  ∀ (F : Type u) [Field F] [NumberField F]
    [NumberField.IsTotallyComplex F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (diagonal F x) = 1) →
  ∀ (r : ℕ) (T Td : CuspidalOperatorRealization F r) (T' Td' : CuspidalOperatorRealization F r),
    OperatorRealization.IsContragredientOf Td.realization T.realization →
    OperatorRealization.IsContragredientOf Td'.realization T'.realization →
  ∀ (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (Pd : CuspidalSpectralPresentation.{u, uQ} Td)
    (Pd' : CuspidalSpectralPresentation.{u, uQ} Td')
    (h : HasIrreducibleAdmissibleComponents P) (h' : HasIrreducibleAdmissibleComponents P')
    (S : Finset (FinitePlace F)) (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
    (hPd : Pd.exceptional ⊆ S) (hPd' : Pd'.exceptional ⊆ S),
    FunctionalEquationComparison.FiniteAdditiveSupport ψ S →
  ∀ (aR : {v : InfinitePlace F // v.IsReal} → ℝˣ),
    (∀ v, IsRealAdditiveComponent ψ v.1 v.2 (aR v)) →
  ∀ (aC : {v : InfinitePlace F // v.IsComplex} → ℂˣ),
    (∀ v, IsComplexAdditiveComponent ψ v.1 v.2 (aC v)) →
  ∀ (dR dR' dRd dRd' : {v : InfinitePlace F // v.IsReal} → List RealBlock),
    (∀ v, OperatorRealization.HasRealPlaceParameter T.realization v (dR v)) →
    (∀ v, OperatorRealization.HasRealPlaceParameter T'.realization v (dR' v)) →
    (∀ v, OperatorRealization.HasRealPlaceParameter Td.realization v (dRd v)) →
    (∀ v, OperatorRealization.HasRealPlaceParameter Td'.realization v (dRd' v)) →
  ∀ (dC dC' dCd dCd' : {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData),
    (∀ v, OperatorRealization.HasComplexPlaceParameter T.realization v (dC v)) →
    (∀ v, OperatorRealization.HasComplexPlaceParameter T'.realization v (dC' v)) →
    (∀ v, OperatorRealization.HasComplexPlaceParameter Td.realization v (dCd v)) →
    (∀ v, OperatorRealization.HasComplexPlaceParameter Td'.realization v (dCd' v)) →
  let infiniteL (s : ℂ) : ℂ :=
    (∏ v, ((realPairLFactor (dR v) (dR' v)).denominator s)⁻¹) *
      ∏ v, ((complexPairLFactor (dC v) (dC' v)).denominator s)⁻¹
  let dualInfiniteL (s : ℂ) : ℂ :=
    (∏ v, ((realPairLFactor (dRd v) (dRd' v)).denominator s)⁻¹) *
      ∏ v, ((complexPairLFactor (dCd v) (dCd' v)).denominator s)⁻¹
  let infiniteEpsilon (s : ℂ) : ℂ :=
    (∏ v, (realPairEpsilon (dR v) (dR' v) (aR v) (NNReal.sqrt ‖((aR v : ℝ))‖₊)
        (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr (aR v).ne_zero)) s : ℂ)) *
      ∏ v, (complexPairEpsilon (dC v) (dC' v) (aC v) ‖((aC v : ℂ))‖₊
        (nnnorm_pos.mpr (aC v).ne_zero) s : ℂ)
  ∃ (σ : ℝ) (I J A B : ℂ → ℂ),
    MeromorphicOn I Set.univ ∧ MeromorphicOn J Set.univ ∧
    MeromorphicOn A Set.univ ∧ MeromorphicOn B Set.univ ∧
    (∀ᶠ s in codiscrete ℂ, A s ≠ 0) ∧ (∀ᶠ s in codiscrete ℂ, B s ≠ 0) ∧
    (∀ᶠ s in codiscrete ℂ, I s = J (1 - s)) ∧
    (∀ s : ℂ, σ < s.re → ∃ p : ℂ,
      HasProd (fun v => partialEulerFactor P P' hP hP' v s) p ∧ I s = A s * p) ∧
    (∀ s : ℂ, σ < s.re → ∃ p : ℂ,
      HasProd (fun v => partialEulerFactor Pd Pd' hPd hPd' v s) p ∧ J s = B s * p) ∧
    ∀ (ψv : ∀ v : FinitePlace F, Correspondence.NontrivialAdditiveCharacter (padicField v)),
      (∀ v, IsCanonicalFiniteAdditiveComponent ψ v (ψv v)) →
    ∀ (νv : ∀ v : FinitePlace F, Correspondence.LocalAdditiveHaarMeasure (padicField v)),
      (∀ v, Correspondence.IsSelfDualMeasure (padicField v) (ψv v) (νv v)) →
    ∀ G : FinitePlace F → RankinSelberg.RationalFunctions,
      (∀ v ∈ S,
        letI := (padicField v).canonicalTopologicalData.topology
        letI := (padicField v).canonicalGeneralLinearTopology (r + 1)
        RankinSelberg.IsPadicSymmetricGammaFactor (padicField v) (ψv v) (νv v)
          ((P.localComponent v).padicObject (h v).1 (h v).2).obj.representation
          ((P'.localComponent v).padicObject (h' v).1 (h' v).2).obj.representation (G v)) →
    ∀ᶠ s in codiscrete ℂ,
      infiniteL s * B (1 - s) =
        (∏ v ∈ S, RatFunc.eval (RingHom.id ℂ)
          (RankinSelberg.spectralPoint (residueCardinality v) s) (G v)) *
          infiniteEpsilon s * dualInfiniteL (1 - s) * A s

/-- The four unrestricted equal-rank premises and the totally complex semi-local equation
give the totally complex equal-rank package. -/
theorem equalPackageTC (hA : RankinSelbergGlobal.EqualAnalyticStatement.{u})
    (hU : RankinSelbergGlobal.EqualUnfoldingStatement.{u})
    (hE : RankinSelbergGlobal.EqualEulerFactorizationStatement.{u, uQ})
    (hD : RankinSelbergGlobal.EqualDualEulerFactorizationStatement.{u, uQ})
    (hS : RankinSelbergGlobal.EqualSemilocalEquationTCStatement.{u, uQ}) :
    EqualPackageTCStatement.{u, uQ} := by
  intro F _ _ _ _ ψ hdiag r T Td T' Td' hTd hTd' P P' Pd Pd' h h' S hP hP' hPd hPd'
    hsupp aR haR aC haC dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd
    hdCd'
  have hstd := isStandardAdditiveCharacter_complex ψ hdiag
  obtain ⟨ω, hω, -⟩ :=
    OperatorRealization.existsUnique_hasCentralCharacter T.realization T.irreducible
  obtain ⟨ω', hω', -⟩ :=
    OperatorRealization.existsUnique_hasCentralCharacter T'.realization T'.irreducible
  obtain ⟨x, x', Φ, hx, hx', hΦ, hΦS, σS, A, B, hAm, hBm, hAeq, hBeq, hA0, hB0, hsem⟩ :=
    hS F ψ hdiag r T Td T' Td' hTd hTd' P P' h h' S hP hP' hsupp aR haR aC haC
      dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd hdCd'
  obtain ⟨C, -, hC⟩ := hU F r T T' ω ω' hω hω'
  obtain ⟨σE, hσE⟩ := hE F ψ hdiag r T T' P P' S hP hP' hsupp
  obtain ⟨σD, hσD⟩ := hD F ψ hdiag r T Td T' Td' hTd hTd' Pd Pd' S hPd hPd' hsupp
  obtain ⟨σ₀, I, Idual, hI0, hIpoles, hIdpoles, -, hIeq⟩ :=
    hA F r T T' ω ω' hω hω' ψ.complex hstd x x' Φ hΦ
  obtain ⟨hU1, hU2⟩ := hC ψ.complex hstd x x' Φ hΦ
  have hfin := equalPoleSet_finite F (r + 1) (ω * ω')
  have hfin' := equalPoleSet_finite F (r + 1) (ω * ω')⁻¹
  refine ⟨max (max σ₀ (1 + C)) (max σE (max σD σS)), I, Idual, A, B,
    meromorphicOn_of_hasAtMostSimplePolesIn hfin hIpoles,
    meromorphicOn_of_hasAtMostSimplePolesIn hfin' hIdpoles, hAm, hBm, hA0, hB0, ?_, ?_, ?_,
    hsem⟩
  · filter_upwards [hfin.compl_mem_codiscrete] with s hs using hIeq s hs
  · intro s hσ
    simp only [max_lt_iff] at hσ
    obtain ⟨⟨h0s, hCs⟩, hEs, -, hSs⟩ := hσ
    obtain ⟨-, -, p, hp, hWp⟩ := hσE x x' Φ hx hx' hΦ hΦS s hEs
    refine ⟨p, hp, ?_⟩
    rw [hAeq s hSs, (hI0 s h0s).2.2.1]
    exact (hU1 s (by linarith)).2.2.trans hWp
  · intro u hσ
    simp only [max_lt_iff] at hσ
    obtain ⟨⟨h0u, hCu⟩, -, hDu, hSu⟩ := hσ
    obtain ⟨-, -, p, hp, hWp⟩ := hσD x x' Φ hx hx' hΦ hΦS u hDu
    refine ⟨p, hp, ?_⟩
    have hu1 : (1 - u).re < -C := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have e2 := (hU2 (1 - u) hu1).2.2
    rw [sub_sub_cancel] at e2
    rw [hBeq u hSu, (hI0 u h0u).2.2.2]
    exact e2.trans hWp

end CuspidalPairPartialGammaTC

/-! ### The reduction -/

/-- The totally complex form of `CuspidalPairPartialGammaGlobalReductionStatement`: the eight
premises of the global Rankin–Selberg theory without archimedean local factors
(Cogdell 2004, §§2–3), unrestricted, and the totally complex forms of the two semi-local
equations imply the totally complex partial equation of cuspidal pairs with integral gamma
factors. The premises are in the order of `CuspidalPairPartialGammaGlobalReductionStatement`. -/
def CuspidalPairPartialGammaGlobalTCReductionStatement : Prop :=
  RankinSelbergGlobal.UnequalAnalyticStatement.{u} →
    RankinSelbergGlobal.UnequalUnfoldingStatement.{u} →
    RankinSelbergGlobal.UnequalEulerFactorizationStatement.{u, uQ} →
    RankinSelbergGlobal.UnequalDualEulerFactorizationStatement.{u, uQ} →
    RankinSelbergGlobal.UnequalSemilocalEquationTCStatement.{u, uQ} →
    RankinSelbergGlobal.EqualAnalyticStatement.{u} →
    RankinSelbergGlobal.EqualUnfoldingStatement.{u} →
    RankinSelbergGlobal.EqualEulerFactorizationStatement.{u, uQ} →
    RankinSelbergGlobal.EqualDualEulerFactorizationStatement.{u, uQ} →
    RankinSelbergGlobal.EqualSemilocalEquationTCStatement.{u, uQ} →
    CuspidalPairPartialGammaEquationTCStatement.{u, uQ}

open CuspidalPairPartialGammaGlobal CuspidalPairPartialGammaTC in
/-- The reduction of the totally complex partial equation of cuspidal pairs to the global
Rankin–Selberg theory with totally complex semi-local equations. The proof is that of
`cuspidalPairPartialGammaGlobalReduction`, with the instance in scope. -/
theorem cuspidalPairPartialGammaGlobalTCReduction :
    CuspidalPairPartialGammaGlobalTCReductionStatement.{u, uQ} := by
  intro hUA hUU hUE hUD hUS hEA hEU hEE hED hES
  have hUP := unequalPackageTC hUA hUU hUE hUD hUS
  have hEP := equalPackageTC hEA hEU hEE hED hES
  classical
  intro F _ _ _ _ ψ _hψ hdiag r t T Td T' Td' hTd hTd' P P' Pd Pd' h h' _hd _hd' S hP hP' hPd
    hPd' hsupp aR haR aC haC dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC'
    hdCd hdCd' infiniteL dualInfiniteL infiniteEpsilon
  have hL : MeromorphicOn infiniteL Set.univ := fun z hz =>
    ((meromorphicOn_prod_inv_denominator Finset.univ
      fun v => realPairLFactor (dR v) (dR' v)) z hz).mul
      ((meromorphicOn_prod_inv_denominator Finset.univ
        fun v => complexPairLFactor (dC v) (dC' v)) z hz)
  have hLd : MeromorphicOn dualInfiniteL Set.univ := fun z hz =>
    ((meromorphicOn_prod_inv_denominator Finset.univ
      fun v => realPairLFactor (dRd v) (dRd' v)) z hz).mul
      ((meromorphicOn_prod_inv_denominator Finset.univ
        fun v => complexPairLFactor (dCd v) (dCd' v)) z hz)
  rcases lt_trichotomy t r with hlt | heq | hgt
  · obtain ⟨σ, I, J, A, B, hI, hJ, hA, hB, hA0, hB0, hIJ, hf, hfd, hsem⟩ :=
      hUP F ψ hdiag r t hlt T Td T' Td' hTd hTd' P P' Pd Pd' h h' S hP hP' hPd hPd' hsupp
        aR haR aC haC dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd hdCd'
    obtain ⟨Λ, Λd, hΛ, hΛd, h1, h2, h3⟩ :=
      exists_partialEquation hL hLd hI hJ hA hB hA0 hB0 hIJ hf hfd
    exact ⟨σ, Λ, Λd, hΛ, hΛd, h1, h2, fun ψv hψv νv hνv G hG =>
      h3 (fun s => (∏ v ∈ S, RatFunc.eval (RingHom.id ℂ)
        (RankinSelberg.spectralPoint (residueCardinality v) s) (G v)) * infiniteEpsilon s)
        (hsem ψv hψv νv hνv G hG)⟩
  · subst heq
    obtain ⟨σ, I, J, A, B, hI, hJ, hA, hB, hA0, hB0, hIJ, hf, hfd, hsem⟩ :=
      hEP F ψ hdiag t T Td T' Td' hTd hTd' P P' Pd Pd' h h' S hP hP' hPd hPd' hsupp
        aR haR aC haC dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd hdCd'
    obtain ⟨Λ, Λd, hΛ, hΛd, h1, h2, h3⟩ :=
      exists_partialEquation hL hLd hI hJ hA hB hA0 hB0 hIJ hf hfd
    exact ⟨σ, Λ, Λd, hΛ, hΛd, h1, h2, fun ψv hψv νv hνv G hG =>
      h3 (fun s => (∏ v ∈ S, RatFunc.eval (RingHom.id ℂ)
        (RankinSelberg.spectralPoint (residueCardinality v) s) (G v)) * infiniteEpsilon s)
        (hsem ψv hψv νv hνv G hG)⟩
  · obtain ⟨σ, I, J, A, B, hI, hJ, hA, hB, hA0, hB0, hIJ, hf, hfd, hsem⟩ :=
      hUP F ψ hdiag t r hgt T' Td' T Td hTd' hTd P' P Pd' Pd h' h S hP' hP hPd' hPd hsupp
        aR haR aC haC dR' dR dRd' dRd hdR' hdR hdRd' hdRd dC' dC dCd' dCd hdC' hdC hdCd' hdCd
    rw [partialEulerFactor_comm P' P hP' hP] at hf
    rw [partialEulerFactor_comm Pd' Pd hPd' hPd] at hfd
    obtain ⟨Λ, Λd, hΛ, hΛd, h1, h2, h3⟩ :=
      exists_partialEquation hL hLd hI hJ hA hB hA0 hB0 hIJ hf hfd
    refine ⟨σ, Λ, Λd, hΛ, hΛd, h1, h2, fun ψv hψv νv hνv G hG => h3
      (fun s => (∏ v ∈ S, RatFunc.eval (RingHom.id ℂ)
        (RankinSelberg.spectralPoint (residueCardinality v) s) (G v)) * infiniteEpsilon s) ?_⟩
    filter_upwards [hsem ψv hψv νv hνv G fun v hv => by
      have hv' := hG v hv
      simp only [RankinSelberg.IsPadicSymmetricGammaFactor, not_le.mpr hgt, hgt.le,
        ↓reduceIte] at hv' ⊢
      exact hv'] with s hs
    simp only [realPairLFactor_denominator_comm (dR' _) (dR _),
      complexPairLFactor_denominator_comm (dC' _) (dC _),
      realPairLFactor_denominator_comm (dRd' _) (dRd _),
      complexPairLFactor_denominator_comm (dCd' _) (dCd _),
      realPairEpsilon_comm (dR' _) (dR _), complexPairEpsilon_comm (dC' _) (dC _)] at hs
    exact hs

end Langlands.Global
