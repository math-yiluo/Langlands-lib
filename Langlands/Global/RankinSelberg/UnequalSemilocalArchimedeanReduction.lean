import Langlands.Global.RankinSelberg.ArchimedeanSemilocalTheoryStatement
import Langlands.Global.RankinSelberg.UnequalSemilocalEquationReduction
import Langlands.Global.RankinSelberg.UnequalSemilocalEquationTCReduction
import Langlands.Global.RankinSelberg.UnequalFactorizationAtStatement

/-! # The unequal-rank semi-local functional equation from the archimedean theory

`unequalSemilocalFactorization_of_archimedean` derives the retained premise
`UnequalSemilocalFactorizationStatement` of the published conditional proof
`unequalSemilocalEquation_of_factorization` from the archimedean Rankin–Selberg statements
of the module `ArchimedeanSemilocalTheoryStatement`: the archimedean local functional
equations (Jacquet 2009, Theorem 2.1; Cogdell 2004, Theorems 3.5–3.6), the factorization of
the partial integrals over `S` and the infinite places, and the central sign (Cogdell 2004,
proof of Theorem 4.1, pp.219–220). Composing the two gives
`UnequalSemilocalArchimedeanReductionStatement`:
`ArchimedeanSemilocalTheoryStatement → UnequalSemilocalEquationStatement`. Over totally
complex fields the complex-place part suffices: `UnequalSemilocalComplexReductionStatement`
is `ComplexSemilocalTheoryStatement → UnequalSemilocalEquationTCStatement`. See the paired
Markdown.
-/

noncomputable section
universe u uQ uF uV uW
open NumberField MeasureTheory
open Langlands.Global.HeckeFunctionalEquation Langlands.Global.CuspidalPairFunctionalEquation
open Langlands.LocalFactor.Archimedean
open Langlands.Global.CompletionPadic Langlands.ClassFieldTheory.Global.RelativeWeilGroup
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

local instance unequalArchimedeanReductionSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance unequalArchimedeanReductionSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

namespace UnequalSemilocalArchimedeanReduction

open UnequalSemilocalReduction

section Local

open Langlands.RankinSelberg HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{uF} p}
  {ψ : letI := K.canonicalTopologicalData.topology; UnitaryAdditiveCharacter K.Carrier}
  {r t : ℕ} {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) K.Carrier) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (t + 1) K.Carrier) W}

/-- If the model of the inverse functional of p-adic test data `D` has minus-one scalar `ζ`,
then `σ` has a nonzero inverse Whittaker functional whose model has minus-one scalar `ζ`
(namely that functional). -/
theorem exists_inverseFunctional_of_hasMinusOneScalar (D : PadicUnequalTestData K ψ π σ)
    {ζ : ℂˣ} (hζ : D.HasMinusOneScalar ζ) :
    letI := K.canonicalTopologicalData.topology
    ∃ ℓ : glInverseFunctionals ψ t σ, ℓ.val ≠ 0 ∧
      RankinSelberg.HasModelMinusOneScalar σ ℓ ζ := by
  let := K.canonicalTopologicalData.topology
  let := K.canonicalTopologicalData.valuativeRel
  let := K.canonicalTopologicalData.localField
  let := borel K.Carrier
  let : BorelSpace K.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (t + 1) K.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (t + 1) K.Carrier) := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear.upperUnipotent (t + 1) K.Carrier)
  let : BorelSpace (Langlands.GeneralLinear.upperUnipotent (t + 1) K.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient t K.Carrier)
  exact ⟨D.inverseFunctional, D.inverseFunctional_ne_zero, hζ⟩

end Local

/-- The algebra of the central sign: the product of the per-place archimedean functional
equations `hPR`, `hPC` and the sign relation `hsg` give the semi-local archimedean equation. -/
theorem sign_identity {c X Y Z LR LC ER EC KR KC NR NC PR PC : ℂ} {r : ℕ}
    (hPR : LR * NR = X ^ r * ER * KR * PR) (hPC : LC * NC = Y ^ r * EC * KC * PC)
    (hsg : (X * Y * Z) ^ r = 1) :
    Z ^ r * (LR * LC) * (c * NR * NC) = ER * EC * (KR * KC) * (c * PR * PC) := by
  linear_combination (c * Z ^ r * (LC * NC)) * hPR + (c * Z ^ r * X ^ r * ER * KR * PR) * hPC +
    (c * ER * EC * KR * KC * PR * PC) * hsg

open Classical in
/-- The body of `UnequalSemilocalFactorizationStatement` over the field `F`. -/
abbrev FactorizationAt (F : Type u) [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] : Prop :=
    ∀ (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
      (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
    ∀ (r t : ℕ) (h : t < r) (T Td : Automorphic.CuspidalOperatorRealization F r)
      (T' Td' : Automorphic.CuspidalOperatorRealization F t),
      Automorphic.OperatorRealization.IsContragredientOf Td.realization T.realization →
      Automorphic.OperatorRealization.IsContragredientOf Td'.realization T'.realization →
    ∀ (P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T)
      (P' : Automorphic.CuspidalSpectralPresentation.{u, uQ} T')
      (hI : HasIrreducibleAdmissibleComponents P) (hI' : HasIrreducibleAdmissibleComponents P')
      (S : Finset (FinitePlace F)), P.exceptional ⊆ S → P'.exceptional ⊆ S →
      FunctionalEquationComparison.FiniteAdditiveSupport ψ S →
    ∀ (aR : {v : InfinitePlace F // v.IsReal} → ℝˣ),
      (∀ v, IsRealAdditiveComponent ψ v.1 v.2 (aR v)) →
    ∀ (aC : {v : InfinitePlace F // v.IsComplex} → ℂˣ),
      (∀ v, IsComplexAdditiveComponent ψ v.1 v.2 (aC v)) →
    ∀ (dR dR' dRd dRd' : {v : InfinitePlace F // v.IsReal} → List RealBlock),
      (∀ v, Automorphic.OperatorRealization.HasRealPlaceParameter T.realization v (dR v)) →
      (∀ v, Automorphic.OperatorRealization.HasRealPlaceParameter T'.realization v (dR' v)) →
      (∀ v, Automorphic.OperatorRealization.HasRealPlaceParameter Td.realization v (dRd v)) →
      (∀ v, Automorphic.OperatorRealization.HasRealPlaceParameter Td'.realization v (dRd' v)) →
    ∀ (dC dC' dCd dCd' : {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData),
      (∀ v, Automorphic.OperatorRealization.HasComplexPlaceParameter T.realization v (dC v)) →
      (∀ v, Automorphic.OperatorRealization.HasComplexPlaceParameter T'.realization v (dC' v)) →
      (∀ v, Automorphic.OperatorRealization.HasComplexPlaceParameter Td.realization v (dCd v)) →
      (∀ v, Automorphic.OperatorRealization.HasComplexPlaceParameter Td'.realization v
        (dCd' v)) →
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
    ∀ (ψv : ∀ v : FinitePlace F, Correspondence.NontrivialAdditiveCharacter (padicField v)),
      (∀ v, IsCanonicalFiniteAdditiveComponent ψ v (ψv v)) →
    ∀ (νv : ∀ v : FinitePlace F, Correspondence.LocalAdditiveHaarMeasure (padicField v)),
      (∀ v, Correspondence.IsSelfDualMeasure (padicField v) (ψv v) (νv v)) →
    ∃ (x : T.Space) (x' : T'.Space), IsSphericalOutside F T S x ∧ IsSphericalOutside F T' S x' ∧
      let W := cuspWhittaker F T ψ.complex x
      let W' := cuspWhittaker F T' ψ.complex⁻¹ x'
      let Wdual := translateFunction F (r + 1) (unfoldingWeyl F h) (dualFunction F (r + 1) W)
      let W'dual := dualFunction F (t + 1) W'
      ∃ (σ : ℝ) (Ainf Binf : ℂ → ℂ)
        (D : ∀ v : S,
          letI := (padicField v.1).canonicalTopologicalData.topology
          letI := (padicField v.1).canonicalGeneralLinearTopology (r + 1)
          letI := (padicField v.1).canonicalGeneralLinearTopology (t + 1)
          PadicUnequalTestData (padicField v.1) (ψv v.1)
            ((P.localComponent v.1).padicObject (hI v.1).1 (hI v.1).2).obj.representation
            ((P'.localComponent v.1).padicObject (hI' v.1).1 (hI' v.1).2).obj.representation),
        MeromorphicOn Ainf Set.univ ∧ MeromorphicOn Binf Set.univ ∧
        (∀ᶠ s in Filter.codiscrete ℂ, Ainf s ≠ 0) ∧ (∀ᶠ s in Filter.codiscrete ℂ, Binf s ≠ 0) ∧
        (∀ v : S, ∃ R : RankinSelberg.RationalFunctions, R ≠ 0 ∧
          RankinSelberg.HasRationalContinuation (residueCardinality v.1)
            ((D v).integral h (νv v.1)) R) ∧
        (∀ s : ℂ, σ < s.re → partialUnequalWhittakerIntegral F h S W W' s =
          Ainf s * ∏ v : S, (D v).integral h (νv v.1) s) ∧
        (∀ s : ℂ, σ < s.re → partialDualWhittakerIntegral F h S Wdual W'dual s =
          Binf s * ∏ v : S, (D v).dualIntegral h (νv v.1) s) ∧
        ∀ ζ : S → ℂˣ, (∀ v : S, (D v).HasMinusOneScalar (ζ v)) →
          ∀ᶠ s in Filter.codiscrete ℂ,
            (∏ v : S, (ζ v : ℂ) ^ r) * infiniteL s * Binf (1 - s) =
              infiniteEpsilon s * dualInfiniteL (1 - s) * Ainf s

open Classical in
/-- The semi-local premise at `F` from the integrated factorization at `F`, the central
sign, and the local functional equations. The real-place input is vacuous if `F` is
totally complex. -/
theorem factorization_of_at
    (hCo : ComplexUnequalFunctionalEquationStatement.{u})
    (hSign : ArchimedeanCentralSignStatement.{u, uQ})
    (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (hFac : UnequalArchimedeanFactorizationAt.{u, uQ} F)
    (hRe : {v : InfinitePlace F // v.IsReal} → RealUnequalFunctionalEquationStatement.{u}) :
    FactorizationAt.{u, uQ} F := by
  intro ψ hdiag r t h T Td T' Td' hTd hTd' P P' hI hI' S hPS hP'S hψS aR haR aC haC
    dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd hdCd' infiniteL
    dualInfiniteL infiniteEpsilon ψv hψv νv hνv
  -- result 2: vectors, archimedean data, local data and the factorizations
  obtain ⟨x, x', hx, hx', hrest⟩ := hFac ψ hdiag r t h T Td T' Td' hTd hTd' P P' hI hI' S
    hPS hP'S hψS aR haR aC haC dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC'
    hdCd hdCd' ψv hψv νv hνv
  obtain ⟨c, WR, WR', DR, WC, WC', DC, σ2, D, hc, hWR, hWR', hWC, hWC', hfacA, hfacB,
    hne, hned, hneS, -⟩ := hrest
  -- result 1 at the real and at the complex places
  have hRv := fun v : {v : InfinitePlace F // v.IsReal} =>
    hRe v F ψ hdiag r t h T Td T' Td' hTd hTd' v (aR v) (haR v) (dR v) (dR' v) (dRd v) (dRd' v)
      (hdR v) (hdR' v) (hdRd v) (hdRd' v) (DR v) (WR v) (WR' v) (hWR v) (hWR' v)
  choose σR MR MdR hiR hidR hdiffR hdiffdR hMR hMdR hMReq hMdReq hFER using hRv
  have hCv := fun w : {v : InfinitePlace F // v.IsComplex} =>
    hCo F ψ hdiag r t h T Td T' Td' hTd hTd' w (aC w) (haC w) (dC w) (dC' w) (dCd w) (dCd' w)
      (hdC w) (hdC' w) (hdCd w) (hdCd' w) (DC w) (WC w) (WC' w) (hWC w) (hWC' w)
  choose σC MC MdC hiC hidC hdiffC hdiffdC hMC hMdC hMCeq hMdCeq hFEC using hCv
  -- a common half-plane
  obtain ⟨σR', hσR⟩ := Finite.exists_le σR
  obtain ⟨σC', hσC⟩ := Finite.exists_le σC
  have hσ2 : ∀ s : ℂ, max σ2 (max σR' σC') < s.re → σ2 < s.re := fun s hs =>
    lt_of_le_of_lt (le_max_left _ _) hs
  have hσRv : ∀ (v : {v : InfinitePlace F // v.IsReal}) (s : ℂ),
      max σ2 (max σR' σC') < s.re → σR v < s.re := fun v s hs =>
    lt_of_le_of_lt ((hσR v).trans ((le_max_left _ _).trans (le_max_right _ _))) hs
  have hσCv : ∀ (w : {v : InfinitePlace F // v.IsComplex}) (s : ℂ),
      max σ2 (max σR' σC') < s.re → σC w < s.re := fun w s hs =>
    lt_of_le_of_lt ((hσC w).trans ((le_max_right _ _).trans (le_max_right _ _))) hs
  have hopen : ∀ a : ℝ, IsOpen {s : ℂ | a < s.re} := fun a =>
    isOpen_lt continuous_const Complex.continuous_re
  -- the archimedean functions
  let Ainf : ℂ → ℂ := fun s => c * (∏ v, MR v s) * ∏ w, MC w s
  let Binf : ℂ → ℂ := fun s => c * (∏ v, MdR v s) * ∏ w, MdC w s
  have hAm : MeromorphicOn Ainf Set.univ :=
    ((MeromorphicOn.const c).mul (MeromorphicOn.fun_prod fun v _ => hMR v)).mul
      (MeromorphicOn.fun_prod fun w _ => hMC w)
  have hBm : MeromorphicOn Binf Set.univ :=
    ((MeromorphicOn.const c).mul (MeromorphicOn.fun_prod fun v _ => hMdR v)).mul
      (MeromorphicOn.fun_prod fun w _ => hMdC w)
  have hAeq : ∀ s : ℂ, max σ2 (max σR' σC') < s.re → Ainf s =
      c * ((∏ v, ArchimedeanLocal.realUnequalIntegral h (DR v) (WR v) (WR' v) s) *
        ∏ w, ArchimedeanLocal.complexUnequalIntegral h (DC w) (WC w) (WC' w) s) := by
    intro s hs
    have e1 : (∏ v, MR v s) =
        ∏ v, ArchimedeanLocal.realUnequalIntegral h (DR v) (WR v) (WR' v) s :=
      Finset.prod_congr rfl fun v _ => (hMReq v s (hσRv v s hs)).symm
    have e2 : (∏ w, MC w s) =
        ∏ w, ArchimedeanLocal.complexUnequalIntegral h (DC w) (WC w) (WC' w) s :=
      Finset.prod_congr rfl fun w _ => (hMCeq w s (hσCv w s hs)).symm
    simp only [Ainf, e1, e2]
    ring
  have hBeq : ∀ s : ℂ, max σ2 (max σR' σC') < s.re → Binf s =
      c * ((∏ v, ArchimedeanLocal.realUnequalDualIntegral h (aR v) (DR v) (WR v) (WR' v) s) *
        ∏ w, ArchimedeanLocal.complexUnequalDualIntegral h (aC w) (DC w) (WC w) (WC' w) s) := by
    intro s hs
    have e1 : (∏ v, MdR v s) =
        ∏ v, ArchimedeanLocal.realUnequalDualIntegral h (aR v) (DR v) (WR v) (WR' v) s :=
      Finset.prod_congr rfl fun v _ => (hMdReq v s (hσRv v s hs)).symm
    have e2 : (∏ w, MdC w s) =
        ∏ w, ArchimedeanLocal.complexUnequalDualIntegral h (aC w) (DC w) (WC w) (WC' w) s :=
      Finset.prod_congr rfl fun w _ => (hMdCeq w s (hσCv w s hs)).symm
    simp only [Binf, e1, e2]
    ring
  -- analyticity on the common half-plane
  have hAan : ∀ s0 : ℂ, max σ2 (max σR' σC') < s0.re → AnalyticAt ℂ Ainf s0 := by
    intro s0 hs0
    have hR : ∀ v ∈ (Finset.univ : Finset {v : InfinitePlace F // v.IsReal}),
        AnalyticAt ℂ (MR v) s0 := fun v _ =>
      ((hdiffR v).analyticAt ((hopen _).mem_nhds (hσRv v s0 hs0))).congr
        (Filter.eventually_of_mem ((hopen _).mem_nhds (hσRv v s0 hs0)) fun s hs => hMReq v s hs)
    have hC : ∀ w ∈ (Finset.univ : Finset {v : InfinitePlace F // v.IsComplex}),
        AnalyticAt ℂ (MC w) s0 := fun w _ =>
      ((hdiffC w).analyticAt ((hopen _).mem_nhds (hσCv w s0 hs0))).congr
        (Filter.eventually_of_mem ((hopen _).mem_nhds (hσCv w s0 hs0)) fun s hs => hMCeq w s hs)
    exact (analyticAt_const.mul (Finset.analyticAt_fun_prod _ hR)).mul
      (Finset.analyticAt_fun_prod _ hC)
  have hBan : ∀ s0 : ℂ, max σ2 (max σR' σC') < s0.re → AnalyticAt ℂ Binf s0 := by
    intro s0 hs0
    have hR : ∀ v ∈ (Finset.univ : Finset {v : InfinitePlace F // v.IsReal}),
        AnalyticAt ℂ (MdR v) s0 := fun v _ =>
      ((hdiffdR v).analyticAt ((hopen _).mem_nhds (hσRv v s0 hs0))).congr
        (Filter.eventually_of_mem ((hopen _).mem_nhds (hσRv v s0 hs0)) fun s hs =>
          hMdReq v s hs)
    have hC : ∀ w ∈ (Finset.univ : Finset {v : InfinitePlace F // v.IsComplex}),
        AnalyticAt ℂ (MdC w) s0 := fun w _ =>
      ((hdiffdC w).analyticAt ((hopen _).mem_nhds (hσCv w s0 hs0))).congr
        (Filter.eventually_of_mem ((hopen _).mem_nhds (hσCv w s0 hs0)) fun s hs =>
          hMdCeq w s hs)
    exact (analyticAt_const.mul (Finset.analyticAt_fun_prod _ hR)).mul
      (Finset.analyticAt_fun_prod _ hC)
  refine ⟨x, x', hx, hx', ?_⟩
  intro W W' Wdual W'dual
  refine ⟨max σ2 (max σR' σC'), Ainf, Binf, D, hAm, hBm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `Ainf` is nonzero off a discrete set
    obtain ⟨s0, hs0, hne0⟩ := hne (max σ2 (max σR' σC'))
    refine EqualSemilocalReduction.eventually_ne_zero_of_analyticAt hAm (hAan s0 hs0) ?_
    rw [hAeq s0 hs0]
    exact mul_ne_zero hc hne0
  · -- `Binf` is nonzero off a discrete set
    obtain ⟨s0, hs0, hne0⟩ := hned (max σ2 (max σR' σC'))
    refine EqualSemilocalReduction.eventually_ne_zero_of_analyticAt hBm (hBan s0 hs0) ?_
    rw [hBeq s0 hs0]
    exact mul_ne_zero hc hne0
  · -- nonzero rational continuations of the local integrals at `S`
    intro v
    have hG : ∃ G : RankinSelberg.RationalFunctions,
        letI := (padicField v.1).canonicalTopologicalData.topology
        letI := (padicField v.1).canonicalGeneralLinearTopology (r + 1)
        letI := (padicField v.1).canonicalGeneralLinearTopology (t + 1)
        RankinSelberg.IsPadicPairGammaFactor (padicField v.1) (ψv v.1) (νv v.1)
          ((P.localComponent v.1).padicObject (hI v.1).1 (hI v.1).2).obj.representation
          ((P'.localComponent v.1).padicObject (hI' v.1).1 (hI' v.1).2).obj.representation
          G := by
      let := (padicField v.1).canonicalTopologicalData.topology
      let := (padicField v.1).canonicalGeneralLinearTopology (r + 1)
      let := (padicField v.1).canonicalGeneralLinearTopology (t + 1)
      have hπ := Automorphic.CuspidalPairPartialGamma.localGenericity.{u, uQ} F r T P v.1
        (hI v.1).1 (hI v.1).2 (ψv v.1)
      have hσ := Automorphic.CuspidalPairPartialGamma.localGenericity.{u, uQ} F t T' P' v.1
        (hI' v.1).1 (hI' v.1).2 (ψv v.1)
      exact ⟨_, RankinSelberg.genericPairGammaFactor_isPadic (padicField v.1) h.le (ψv v.1)
        (νv v.1) (hνv v.1) _ _ hπ hσ⟩
    obtain ⟨G, hG⟩ := hG
    obtain ⟨-, -, R, -, hR, -, -⟩ := PadicUnequalTestData.exists_gammaEquation h (D v) hG
    refine ⟨R, ?_, hR⟩
    rintro rfl
    obtain ⟨a, ha⟩ := hR
    obtain ⟨s, hs, hs0⟩ := hneS v a
    exact hs0 (by rw [(ha s hs).2, RatFunc.eval_zero])
  · -- factorization of the partial integral
    intro s hs
    rw [hfacA s (hσ2 s hs), hAeq s hs]
  · -- factorization of the dual partial integral
    intro s hs
    rw [hfacB s (hσ2 s hs), hBeq s hs]
  · -- the functional equation over the infinite places, with the central sign
    intro ζ hζ
    have hsg := hSign F t T' P' hI' S hP'S ψv ζ fun v =>
      exists_inverseFunctional_of_hasMinusOneScalar (D v) (hζ v)
    filter_upwards [Filter.eventually_all.mpr hFER, Filter.eventually_all.mpr hFEC]
      with s hsR hsC
    have hPR :
        (∏ v, ((realPairLFactor (dR v) (dR' v)).denominator s)⁻¹) * (∏ v, MdR v (1 - s)) =
          (∏ v, realMinusOneScalar T' v) ^ r *
            (∏ v, (realPairEpsilon (dR v) (dR' v) (aR v) (NNReal.sqrt ‖((aR v : ℝ))‖₊)
              (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr (aR v).ne_zero)) s : ℂ)) *
            (∏ v, ((realPairLFactor (dRd v) (dRd' v)).denominator (1 - s))⁻¹) *
            ∏ v, MR v s := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_pow, ← Finset.prod_mul_distrib,
        ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun v _ => hsR v
    have hPC :
        (∏ w, ((complexPairLFactor (dC w) (dC' w)).denominator s)⁻¹) * (∏ w, MdC w (1 - s)) =
          (∏ w, complexMinusOneScalar T' w) ^ r *
            (∏ w, (complexPairEpsilon (dC w) (dC' w) (aC w) ‖((aC w : ℂ))‖₊
              (nnnorm_pos.mpr (aC w).ne_zero) s : ℂ)) *
            (∏ w, ((complexPairLFactor (dCd w) (dCd' w)).denominator (1 - s))⁻¹) *
            ∏ w, MC w s := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_pow, ← Finset.prod_mul_distrib,
        ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun w _ => hsC w
    have hsgr : ((∏ v, realMinusOneScalar T' v) * (∏ w, complexMinusOneScalar T' w) *
        ∏ v : S, (ζ v : ℂ)) ^ r = 1 := by
      rw [hsg, one_pow]
    simp only [infiniteL, dualInfiniteL, infiniteEpsilon, Ainf, Binf, Finset.prod_pow]
    exact sign_identity hPR hPC hsgr

/-- The semi-local premise at `F`, using an integrated factorization given over all number
fields. -/
theorem factorization_at
    (hCo : ComplexUnequalFunctionalEquationStatement.{u})
    (hFac : UnequalArchimedeanFactorizationStatement.{u, uQ})
    (hSign : ArchimedeanCentralSignStatement.{u, uQ})
    (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (hRe : {v : InfinitePlace F // v.IsReal} → RealUnequalFunctionalEquationStatement.{u}) :
    FactorizationAt.{u, uQ} F :=
  factorization_of_at hCo hSign F (hFac F) hRe

/-- The premise `UnequalSemilocalFactorizationStatement` from the four unequal-rank parts of
the archimedean theory: the real-place and complex-place functional equations, the
factorization and the central sign. -/
theorem unequalSemilocalFactorization_of_parts
    (hRe : RealUnequalFunctionalEquationStatement.{u})
    (hCo : ComplexUnequalFunctionalEquationStatement.{u})
    (hFac : UnequalArchimedeanFactorizationStatement.{u, uQ})
    (hSign : ArchimedeanCentralSignStatement.{u, uQ}) :
    UnequalSemilocalFactorizationStatement.{u, uQ} := by
  intro F _ _ _
  exact factorization_at hCo hFac hSign F fun _ => hRe

/-- The totally complex premise `UnequalSemilocalFactorizationTCStatement` from the
complex-place unequal-rank functional equation, the factorization and the central sign: a
totally complex field has no real place, so the real-place hypothesis of `factorization_at`
holds vacuously. -/
theorem unequalSemilocalFactorizationTC_of_parts
    (hCo : ComplexUnequalFunctionalEquationStatement.{u})
    (hFac : UnequalArchimedeanFactorizationStatement.{u, uQ})
    (hSign : ArchimedeanCentralSignStatement.{u, uQ}) :
    UnequalSemilocalFactorizationTCStatement.{u, uQ} := by
  intro F _ _ _ _
  exact factorization_at hCo hFac hSign F fun v =>
    (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex v.1) v.2).elim

end UnequalSemilocalArchimedeanReduction

open UnequalSemilocalArchimedeanReduction

/-- **Cogdell 2004, proof of Theorem 4.1, pp.219–220, with §3.2** (derivation of the
premise): the archimedean semi-local theory implies the premise
`UnequalSemilocalFactorizationStatement`. -/
theorem unequalSemilocalFactorization_of_archimedean
    (hA : ArchimedeanSemilocalTheoryStatement.{u, uQ}) :
    UnequalSemilocalFactorizationStatement.{u, uQ} :=
  unequalSemilocalFactorization_of_parts hA.1.2.1 hA.1.1.1 hA.2.1.1 hA.2.2

/-- **Conditional reduction** (Cogdell 2004, proof of Theorem 4.1, pp.219–220): the
archimedean semi-local theory `ArchimedeanSemilocalTheoryStatement` implies the semi-local
functional equation `UnequalSemilocalEquationStatement`. Proved below by
`unequalSemilocalArchimedeanReduction`. -/
def UnequalSemilocalArchimedeanReductionStatement : Prop :=
  ArchimedeanSemilocalTheoryStatement.{u, uQ} → UnequalSemilocalEquationStatement.{u, uQ}

/-- Proof of `UnequalSemilocalArchimedeanReductionStatement`: the derivation of the premise,
followed by the published `unequalSemilocalEquation_of_factorization`. -/
theorem unequalSemilocalArchimedeanReduction :
    UnequalSemilocalArchimedeanReductionStatement.{u, uQ} := fun hA =>
  unequalSemilocalEquation_of_factorization (unequalSemilocalFactorization_of_archimedean hA)

/-- **Cogdell 2004, proof of Theorem 4.1, totally complex fields** (derivation of the
premise): the complex-place semi-local theory implies the premise
`UnequalSemilocalFactorizationTCStatement`. -/
theorem unequalSemilocalFactorizationTC_of_complex
    (hC : ComplexSemilocalTheoryStatement.{u, uQ}) :
    UnequalSemilocalFactorizationTCStatement.{u, uQ} :=
  unequalSemilocalFactorizationTC_of_parts hC.1.1 hC.2.1.1 hC.2.2

/-- **Conditional reduction, totally complex fields** (Cogdell 2004, proof of Theorem 4.1,
pp.219–220): the complex-place semi-local theory `ComplexSemilocalTheoryStatement` implies
`UnequalSemilocalEquationTCStatement`. Proved below by `unequalSemilocalComplexReduction`. -/
def UnequalSemilocalComplexReductionStatement : Prop :=
  ComplexSemilocalTheoryStatement.{u, uQ} → UnequalSemilocalEquationTCStatement.{u, uQ}

/-- Proof of `UnequalSemilocalComplexReductionStatement`: the derivation of the totally
complex premise, followed by the published `unequalSemilocalEquationTC_of_factorizationTC`. -/
theorem unequalSemilocalComplexReduction :
    UnequalSemilocalComplexReductionStatement.{u, uQ} := fun hC =>
  unequalSemilocalEquationTC_of_factorizationTC (unequalSemilocalFactorizationTC_of_complex hC)

end Langlands.Global.RankinSelbergGlobal
