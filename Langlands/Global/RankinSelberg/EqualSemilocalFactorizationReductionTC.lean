import Langlands.Global.RankinSelberg.EqualSemilocalFactorizationReduction
import Langlands.Global.RankinSelberg.EqualFactorizationAtStatement
import Langlands.Global.RankinSelberg.EqualSemilocalReductionTC

/-! # Totally complex reduction of the equal-rank factorization premise

`EqualSemilocalFactorizationTCStatement`, the totally complex form of the premise of the
equal-rank semi-local reduction, follows from the equal-rank archimedean functional equation at
the complex places (Jacquet 2009, Theorem 2.1), the equal-rank factorization over `S` and the
infinite places (Cogdell 2004, p.220) and the central sign (Cogdell 2004, p.220). The real-place
functional equation is not needed: a totally complex field has no real place. See the paired
Markdown.
-/

noncomputable section
universe u uQ
open NumberField MeasureTheory Filter Topology
open Langlands.Global.HeckeFunctionalEquation Langlands.Global.CuspidalPairFunctionalEquation
open Langlands.LocalFactor.Archimedean
open Langlands.Global.CompletionPadic Langlands.ClassFieldTheory.Global.RelativeWeilGroup
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

local instance equalFactorizationReductionTCSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance equalFactorizationReductionTCSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

/-- **The totally complex reduction of the equal-rank factorization premise**: the equal-rank
archimedean functional equation at the complex places, the equal-rank factorization over `S`
and the infinite places, and the central sign imply `EqualSemilocalFactorizationTCStatement`. -/
def EqualSemilocalFactorizationReductionTCStatement : Prop :=
  ComplexEqualFunctionalEquationStatement.{u} →
    EqualArchimedeanFactorizationStatement.{u, uQ} → ArchimedeanCentralSignStatement.{u, uQ} →
      EqualSemilocalFactorizationTCStatement.{u, uQ}

open EqualSemilocalFactorizationReduction in
/-- **The totally complex reduction of the equal-rank factorization premise**: the proof of
`equalSemilocalFactorizationReduction`, with the real-place facts proved vacuously. -/
theorem equalSemilocalFactorizationTC_of_factorizationTC
    (hC : ComplexEqualFunctionalEquationStatement.{u})
    (h2 : EqualArchimedeanFactorizationTCStatement.{u, uQ})
    (h3 : ArchimedeanCentralSignStatement.{u, uQ}) :
    EqualSemilocalFactorizationTCStatement.{u, uQ} := by
  intro F _ _ _ _ ψ hdiag r T Td T' Td' hTd hTd' P P' hI hI' S hPS hP'S hsupp aR haR
    aC haC dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd hdCd'
    infiniteL dualInfiniteL infiniteEpsilon ψv hψv νv hνv
  classical
  -- a totally complex field has no real place
  have hnoreal : ∀ v : {v : InfinitePlace F // v.IsReal}, False := fun v =>
    InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex v.1) v.2
  obtain ⟨x, x', Φ, hx, hx', hΦ, hΦS, hrest⟩ :=
    h2 F ψ hdiag r T Td T' Td' hTd hTd' P P' hI hI' S hPS hP'S hsupp aR haR aC haC
      dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd hdCd' ψv hψv νv hνv
  refine ⟨x, x', Φ, hx, hx', hΦ, hΦS, ?_⟩
  intro W W' Wdual W'dual Φhat
  obtain ⟨c, WR, WR', ΦR, DR, WC, WC', ΦC, DC, σ₂, D, hc, hWR, hWR', hWC, hWC', -, -,
    hfacA, hfacB, hinf, hinfd, hDne, hDdne⟩ := hrest
  beta_reduce at hfacA hfacB hinf hinfd
  -- the facts used at the real places, vacuously (there is no real place)
  have hRF : ∀ v : {v : InfinitePlace F // v.IsReal}, ∃ (σ : ℝ) (M Md : ℂ → ℂ),
      DifferentiableOn ℂ (ArchimedeanLocal.realEqualIntegral (DR v) (WR v) (WR' v) (ΦR v))
        {s : ℂ | σ < s.re} ∧
      DifferentiableOn ℂ
        (ArchimedeanLocal.realEqualDualIntegral (aR v) (DR v) (WR v) (WR' v) (ΦR v))
        {s : ℂ | σ < s.re} ∧
      MeromorphicOn M Set.univ ∧ MeromorphicOn Md Set.univ ∧
      (∀ s : ℂ, σ < s.re →
        ArchimedeanLocal.realEqualIntegral (DR v) (WR v) (WR' v) (ΦR v) s = M s) ∧
      (∀ s : ℂ, σ < s.re →
        ArchimedeanLocal.realEqualDualIntegral (aR v) (DR v) (WR v) (WR' v) (ΦR v) s = Md s) ∧
      ∀ᶠ s in Filter.codiscrete ℂ,
        ((realPairLFactor (dR v) (dR' v)).denominator s)⁻¹ * Md (1 - s) =
          realMinusOneScalar T' v ^ r *
            (realPairEpsilon (dR v) (dR' v) (aR v) (NNReal.sqrt ‖((aR v : ℝ))‖₊)
              (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr (aR v).ne_zero)) s : ℂ) *
            ((realPairLFactor (dRd v) (dRd' v)).denominator (1 - s))⁻¹ * M s :=
    fun v => (hnoreal v).elim
  choose σR MR MdR hRdiff hRdiffd hRmer hRmerd hReq hReqd hRfe using hRF
  -- the archimedean functional equation at each complex place
  choose σC MC MdC hCint hCintd hCdiff hCdiffd hCmer hCmerd hCeq hCeqd hCfe using
    fun w : {v : InfinitePlace F // v.IsComplex} =>
      hC F ψ hdiag r T Td T' Td' hTd hTd' w (aC w) (haC w) (dC w) (dC' w) (dCd w) (dCd' w)
        (hdC w) (hdC' w) (hdCd w) (hdCd' w) (DC w) (WC w) (WC' w) (ΦC w) (hWC w) (hWC' w)
  -- a common half-plane
  obtain ⟨σ, hσ₂, hσR, hσC⟩ : ∃ σ : ℝ, σ₂ ≤ σ ∧ (∀ v, σR v ≤ σ) ∧ ∀ w, σC w ≤ σ := by
    obtain ⟨a, ha⟩ := Finite.exists_le σR
    obtain ⟨b, hb⟩ := Finite.exists_le σC
    exact ⟨max σ₂ (max a b), le_max_left _ _,
      fun v => (ha v).trans ((le_max_left _ _).trans (le_max_right _ _)),
      fun w => (hb w).trans ((le_max_right _ _).trans (le_max_right _ _))⟩
  have h2s : ∀ s : ℂ, σ < s.re → σ₂ < s.re := fun s hs => lt_of_le_of_lt hσ₂ hs
  have hRs : ∀ v (s : ℂ), σ < s.re → σR v < s.re := fun v s hs => lt_of_le_of_lt (hσR v) hs
  have hCs : ∀ w (s : ℂ), σ < s.re → σC w < s.re := fun w s hs => lt_of_le_of_lt (hσC w) hs
  -- the products of the archimedean integrals agree with the products of continuations
  have hprod : ∀ s : ℂ, σ < s.re →
      (∏ v, ArchimedeanLocal.realEqualIntegral (DR v) (WR v) (WR' v) (ΦR v) s) *
          ∏ w, ArchimedeanLocal.complexEqualIntegral (DC w) (WC w) (WC' w) (ΦC w) s =
        (∏ v, MR v s) * ∏ w, MC w s := fun s hs => by
    rw [Finset.prod_congr rfl fun v _ => hReq v s (hRs v s hs),
      Finset.prod_congr rfl fun w _ => hCeq w s (hCs w s hs)]
  have hprodd : ∀ s : ℂ, σ < s.re →
      (∏ v, ArchimedeanLocal.realEqualDualIntegral (aR v) (DR v) (WR v) (WR' v) (ΦR v) s) *
          ∏ w, ArchimedeanLocal.complexEqualDualIntegral (aC w) (DC w) (WC w) (WC' w) (ΦC w) s =
        (∏ v, MdR v s) * ∏ w, MdC w s := fun s hs => by
    rw [Finset.prod_congr rfl fun v _ => hReqd v s (hRs v s hs),
      Finset.prod_congr rfl fun w _ => hCeqd w s (hCs w s hs)]
  -- the archimedean parts `Z` and `Zd`
  have hZmer : MeromorphicOn (fun s => c * (∏ v, MR v s) * ∏ w, MC w s) Set.univ :=
    ((MeromorphicOn.const c).mul (MeromorphicOn.fun_prod fun v _ => hRmer v)).mul
      (MeromorphicOn.fun_prod fun w _ => hCmer w)
  have hZdmer : MeromorphicOn (fun s => c * (∏ v, MdR v s) * ∏ w, MdC w s) Set.univ :=
    ((MeromorphicOn.const c).mul (MeromorphicOn.fun_prod fun v _ => hRmerd v)).mul
      (MeromorphicOn.fun_prod fun w _ => hCmerd w)
  refine ⟨σ, fun s => c * (∏ v, MR v s) * ∏ w, MC w s,
    fun s => c * (∏ v, MdR v s) * ∏ w, MdC w s,
    (∏ v, realMinusOneScalar T' v ^ r) * ∏ w, complexMinusOneScalar T' w ^ r,
    hZmer, hZdmer, ?_, ?_, ?_, D, hDne, hDdne, ?_, ?_, ?_⟩
  · -- `Z` is nonzero off a discrete set
    obtain ⟨s₀, hs₀, hne⟩ := hinf σ
    have han : AnalyticAt ℂ (fun s => c * (∏ v, MR v s) * ∏ w, MC w s) s₀ :=
      (analyticAt_const.mul (Finset.univ.analyticAt_fun_prod fun v _ =>
        analyticAt_of_eq_on_halfPlane (hRdiff v) (hReq v) (hRs v s₀ hs₀))).mul
        (Finset.univ.analyticAt_fun_prod fun w _ =>
          analyticAt_of_eq_on_halfPlane (hCdiff w) (hCeq w) (hCs w s₀ hs₀))
    refine EqualSemilocalReduction.eventually_ne_zero_of_analyticAt hZmer han ?_
    show c * (∏ v, MR v s₀) * ∏ w, MC w s₀ ≠ 0
    rw [mul_assoc, ← hprod s₀ hs₀]
    exact mul_ne_zero hc hne
  · -- `Zd` is nonzero off a discrete set
    obtain ⟨s₀, hs₀, hne⟩ := hinfd σ
    have han : AnalyticAt ℂ (fun s => c * (∏ v, MdR v s) * ∏ w, MdC w s) s₀ :=
      (analyticAt_const.mul (Finset.univ.analyticAt_fun_prod fun v _ =>
        analyticAt_of_eq_on_halfPlane (hRdiffd v) (hReqd v) (hRs v s₀ hs₀))).mul
        (Finset.univ.analyticAt_fun_prod fun w _ =>
          analyticAt_of_eq_on_halfPlane (hCdiffd w) (hCeqd w) (hCs w s₀ hs₀))
    refine EqualSemilocalReduction.eventually_ne_zero_of_analyticAt hZdmer han ?_
    show c * (∏ v, MdR v s₀) * ∏ w, MdC w s₀ ≠ 0
    rw [mul_assoc, ← hprodd s₀ hs₀]
    exact mul_ne_zero hc hne
  · -- the archimedean functional equation: the product over the infinite places
    filter_upwards [Filter.eventually_all.2 hRfe, Filter.eventually_all.2 hCfe] with s hRv hCw
    have hRprod := Finset.prod_congr (s₁ := Finset.univ) rfl fun v _ => hRv v
    have hCprod := Finset.prod_congr (s₁ := Finset.univ) rfl fun w _ => hCw w
    simp only [Finset.prod_mul_distrib] at hRprod hCprod
    exact mul_combine hRprod hCprod
  · -- the sign
    intro ζ hζ
    have hsgn := h3 F r T' P' hI' S hP'S ψv ζ fun v => ⟨(D v).ℓ', (D v).ℓ'_ne_zero, hζ v⟩
    rw [Finset.prod_pow, Finset.prod_pow, Finset.prod_pow, ← mul_pow, ← mul_pow, hsgn,
      one_pow]
  · -- the factorization of the partial integral
    intro s hs
    rw [hfacA s (h2s s hs), hprod s hs]
    ring
  · -- the factorization of the dual partial integral
    intro s hs
    rw [hfacB s (h2s s hs), hprodd s hs]
    ring

/-- Specialize the unrestricted integrated factorization to the totally complex fields. -/
theorem equalSemilocalFactorizationReductionTC :
    EqualSemilocalFactorizationReductionTCStatement.{u, uQ} := by
  intro hC h2 h3
  exact equalSemilocalFactorizationTC_of_factorizationTC hC (fun F _ _ _ _ => h2 F) h3

/-- The conjunction `ArchimedeanSemilocalTheoryStatement` (results 1–3 of the archimedean
theory, both ranks) implies `EqualSemilocalFactorizationTCStatement`. -/
theorem equalSemilocalFactorizationTC_of_archimedeanSemilocalTheory
    (h : ArchimedeanSemilocalTheoryStatement.{u, uQ}) :
    EqualSemilocalFactorizationTCStatement.{u, uQ} :=
  equalSemilocalFactorizationReductionTC h.1.1.2 h.2.1.2 h.2.2

/-- The totally complex equal-rank semi-local functional equation
`EqualSemilocalEquationTCStatement` follows from the three premises of
`EqualSemilocalFactorizationReductionTCStatement`, by `equalSemilocalReductionTC`. -/
theorem equalSemilocalEquationTC_of_archimedean
    (hC : ComplexEqualFunctionalEquationStatement.{u})
    (h2 : EqualArchimedeanFactorizationStatement.{u, uQ})
    (h3 : ArchimedeanCentralSignStatement.{u, uQ}) :
    EqualSemilocalEquationTCStatement.{u, uQ} :=
  equalSemilocalReductionTC (equalSemilocalFactorizationReductionTC hC h2 h3)

end Langlands.Global.RankinSelbergGlobal
