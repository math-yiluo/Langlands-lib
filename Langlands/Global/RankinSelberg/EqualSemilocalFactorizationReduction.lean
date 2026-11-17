import Langlands.Global.RankinSelberg.ArchimedeanSemilocalTheoryStatement
import Langlands.Global.RankinSelberg.EqualSemilocalReduction

/-! # Reduction of the equal-rank factorization premise to the archimedean theory

`EqualSemilocalFactorizationStatement`, the premise of the equal-rank semi-local reduction
`equalSemilocalReduction`, follows from three statements of the Library:
the equal-rank archimedean functional equations at the complex and at the real places
(Jacquet 2009, Theorem 2.1), the equal-rank factorization over `S` and the infinite places
(Cogdell 2004, p.220) and the central sign (Cogdell 2004, p.220). See the paired Markdown.
-/

noncomputable section
universe u uQ
open NumberField MeasureTheory Filter Topology
open Langlands.Global.HeckeFunctionalEquation Langlands.Global.CuspidalPairFunctionalEquation
open Langlands.LocalFactor.Archimedean
open Langlands.Global.CompletionPadic Langlands.ClassField.Global.RelativeWeilGroup
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

local instance equalFactorizationReductionSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance equalFactorizationReductionSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

namespace EqualSemilocalFactorizationReduction

/-- A function that agrees on an open right half-plane with a function holomorphic there is
analytic at every point of the half-plane. -/
theorem analyticAt_of_eq_on_halfPlane {f g : ℂ → ℂ} {σ : ℝ}
    (hf : DifferentiableOn ℂ f {s : ℂ | σ < s.re}) (hfg : ∀ s : ℂ, σ < s.re → f s = g s)
    {s : ℂ} (hs : σ < s.re) : AnalyticAt ℂ g s := by
  have hopen : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hg : DifferentiableOn ℂ g {s : ℂ | σ < s.re} :=
    hf.congr fun z hz => (hfg z hz).symm
  exact hg.analyticAt (hopen.mem_nhds hs)

/-- The algebra of the product of the real-place and the complex-place functional equations,
multiplied by the constant `c`. -/
theorem mul_combine {A A' B B' X X' Y Y' E E' N N' c : ℂ}
    (h1 : A * B = X * Y * E * N) (h2 : A' * B' = X' * Y' * E' * N') :
    A * A' * (c * B * B') = X * X' * (Y * Y') * (E * E') * (c * N * N') := by
  linear_combination (c * A' * B') * h1 + (c * X * Y * E * N) * h2

end EqualSemilocalFactorizationReduction

/-- **The reduction of the equal-rank factorization premise**: the equal-rank archimedean
functional equations at the complex and at the real places, the equal-rank factorization
over `S` and the infinite places, and the central sign imply
`EqualSemilocalFactorizationStatement`. -/
def EqualSemilocalFactorizationReductionStatement : Prop :=
  ComplexEqualFunctionalEquationStatement.{u} → RealEqualFunctionalEquationStatement.{u} →
    EqualArchimedeanFactorizationStatement.{u, uQ} → ArchimedeanCentralSignStatement.{u, uQ} →
      EqualSemilocalFactorizationStatement.{u, uQ}

open EqualSemilocalFactorizationReduction in
/-- **The reduction of the equal-rank factorization premise** to the archimedean theory. -/
theorem equalSemilocalFactorizationReduction :
    EqualSemilocalFactorizationReductionStatement.{u, uQ} := by
  intro hC hR h2 h3 F _ _ _ ψ hdiag r T Td T' Td' hTd hTd' P P' hI hI' S hPS hP'S hsupp aR haR
    aC haC dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd hdCd'
    infiniteL dualInfiniteL infiniteEpsilon ψv hψv νv hνv
  classical
  obtain ⟨x, x', Φ, hx, hx', hΦ, hΦS, hrest⟩ :=
    h2 F ψ hdiag r T Td T' Td' hTd hTd' P P' hI hI' S hPS hP'S hsupp aR haR aC haC
      dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd hdCd' ψv hψv νv hνv
  refine ⟨x, x', Φ, hx, hx', hΦ, hΦS, ?_⟩
  intro W W' Wdual W'dual Φhat
  obtain ⟨c, WR, WR', ΦR, DR, WC, WC', ΦC, DC, σ₂, D, hc, hWR, hWR', hWC, hWC', -, -,
    hfacA, hfacB, hinf, hinfd, hDne, hDdne⟩ := hrest
  beta_reduce at hfacA hfacB hinf hinfd
  -- the archimedean functional equation at each real place
  choose σR MR MdR hRint hRintd hRdiff hRdiffd hRmer hRmerd hReq hReqd hRfe using
    fun v : {v : InfinitePlace F // v.IsReal} =>
      hR F ψ hdiag r T Td T' Td' hTd hTd' v (aR v) (haR v) (dR v) (dR' v) (dRd v) (dRd' v)
        (hdR v) (hdR' v) (hdRd v) (hdRd' v) (DR v) (WR v) (WR' v) (ΦR v) (hWR v) (hWR' v)
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

/-- The conjunction `ArchimedeanSemilocalTheoryStatement` (results 1–3 of the archimedean
theory, both ranks) implies `EqualSemilocalFactorizationStatement`. -/
theorem equalSemilocalFactorization_of_archimedeanSemilocalTheory
    (h : ArchimedeanSemilocalTheoryStatement.{u, uQ}) :
    EqualSemilocalFactorizationStatement.{u, uQ} :=
  equalSemilocalFactorizationReduction h.1.1.2 h.1.2.2 h.2.1.2 h.2.2

end Langlands.Global.RankinSelbergGlobal
