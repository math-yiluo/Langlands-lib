import Langlands.Global.Factors.CuspidalPairFiniteEulerContinuity
import Langlands.Global.Factors.CuspidalPairPoleFiniteComparison
import Langlands.Global.Factors.CuspidalPairRightStripBounds

/-! # Left vertical lines from the completed pair functional equation -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Filter NumberField Set
open scoped Topology

universe u uQ

namespace Langlands.Global.CuspidalPairPoles

open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation)
open CuspidalPairFunctionalEquation
open CuspidalPairEulerConvergence
open LocalFactor.Archimedean

/-- A function admits a norm bound on a vertical line to the left of every
prescribed real abscissa. -/
def HasLeftVerticalLineBounds (Λ : ℂ → ℂ) : Prop :=
  ∀ a : ℝ, ∃ l < a, ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re = l → ‖Λ s‖ ≤ C

private theorem analyticAt_of_poleProfile {Λ : ℂ → ℂ} {cond : Prop}
    (hΛ : HasSimplePoleProfile Λ cond) {s : ℂ} (hs : s ∉ ({0, 1} : Set ℂ)) :
    AnalyticAt ℂ Λ s := by
  have hopen : IsOpen ({0, 1} : Set ℂ)ᶜ :=
    ((Set.finite_singleton (1 : ℂ)).insert 0).isClosed.isOpen_compl
  exact hΛ.1.analyticAt (hopen.mem_nhds hs)

private theorem eventuallyEq_codiscrete_of_eq_on_right {f g : ℂ → ℂ}
    (hf : MeromorphicOn f univ) (hg : MeromorphicOn g univ)
    {a : ℝ} (he : ∀ s : ℂ, a < s.re → f s = g s) :
    f =ᶠ[codiscrete ℂ] g := by
  let z : ℂ := (a + 1 : ℝ)
  have hza : a < z.re := by change a < a + 1; linarith
  have hz : (f - g) =ᶠ[𝓝[≠] z] 0 := by
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hza] with s hs
    simp only [Pi.sub_apply, Pi.zero_apply, he s hs, sub_self]
  have hm := hf.sub hg
  have ho := meromorphicOrderAt_eq_top_iff.mpr hz
  refine eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE.mpr (fun s => ?_)
  have hs := hm.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
    (mem_univ z) (mem_univ s) ho
  exact (eventuallyEq_iff_sub).mpr (meromorphicOrderAt_eq_top_iff.mp hs)

private theorem hasLeftVerticalLineBounds_of_equation {Λ D E : ℂ → ℂ} {cond : Prop}
    (hΛ : HasSimplePoleProfile Λ cond) (hE : Continuous E)
    (hEn : ∀ s t : ℂ, s.re = t.re → ‖E s‖ = ‖E t‖)
    {σ : ℝ} (hD : ContinuousOn D {s | σ < s.re})
    (hDb : ∀ b : ℝ, σ < b → ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re = b → ‖D s‖ ≤ C)
    (hEq : ∀ᶠ s : ℂ in codiscrete ℂ, Λ s = E s * D (1 - s)) :
    HasLeftVerticalLineBounds Λ := by
  intro a
  let l := min (min a 0) (1 - σ) - 1
  have hl : l < min (min a 0) (1 - σ) := sub_lt_self _ zero_lt_one
  have hl₀ : l < 0 := hl.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hlσ : σ < 1 - l := by linarith [hl.trans_le (min_le_right (min a 0) (1 - σ))]
  obtain ⟨C, hC, hB⟩ := hDb (1 - l) hlσ
  refine ⟨l, hl.trans_le ((min_le_left _ _).trans (min_le_left _ _)),
    ‖E (l : ℂ)‖ * C, mul_nonneg (norm_nonneg _) hC, ?_⟩
  intro s hs
  have hsr : (1 - s).re = 1 - l := by simp [Complex.sub_re, hs]
  have hsL : s.re < 0 := hs ▸ hl₀
  have haway : s ∉ ({0, 1} : Set ℂ) := by
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨fun he => by rw [he, Complex.zero_re] at hsL; linarith,
      fun he => by rw [he, Complex.one_re] at hsL; linarith⟩
  have hsr' : σ < (1 - s).re := by rw [hsr]; exact hlσ
  have hDc : ContinuousAt D (1 - s) := (hD (1 - s) hsr').continuousAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hsr')
  have hRc : ContinuousAt (fun z : ℂ => E z * D (1 - z)) s :=
    hE.continuousAt.mul (hDc.comp (continuous_const.sub continuous_id).continuousAt)
  have he : Λ =ᶠ[𝓝[≠] s] (fun z => E z * D (1 - z)) := hEq.filter_mono (nhdsNE_le_codiscrete s)
  have hΛc := (analyticAt_of_poleProfile hΛ haway).continuousAt
  have heq := ((hΛc.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hRc).mp he).eq_of_nhds
  rw [heq, norm_mul, hEn s (l : ℂ) hs]
  exact mul_le_mul_of_nonneg_left (hB (1 - s) hsr) (norm_nonneg _)

variable {F : Type u} [Field F] [NumberField F]

/-- The archimedean epsilon product in the completed functional equation. -/
def archimedeanPairEpsilonProduct
    (dR dR' : {v : InfinitePlace F // v.IsReal} → List RealBlock)
    (dC dC' : {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData)
    (aR : {v : InfinitePlace F // v.IsReal} → ℝˣ)
    (aC : {v : InfinitePlace F // v.IsComplex} → ℂˣ) (s : ℂ) : ℂ := by
  classical
  exact
    (∏ v, (realPairEpsilon (dR v) (dR' v) (aR v) (NNReal.sqrt ‖(aR v : ℝ)‖₊)
      (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr (aR v).ne_zero)) s : ℂ)) *
    ∏ v, (complexPairEpsilon (dC v) (dC' v) (aC v) ‖(aC v : ℂ)‖₊
      (nnnorm_pos.mpr (aC v).ne_zero) s : ℂ)

private theorem continuous_archimedeanPairEpsilonProduct
    (dR dR' : {v : InfinitePlace F // v.IsReal} → List RealBlock)
    (dC dC' : {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData)
    (aR : {v : InfinitePlace F // v.IsReal} → ℝˣ)
    (aC : {v : InfinitePlace F // v.IsComplex} → ℂˣ) :
    Continuous (archimedeanPairEpsilonProduct dR dR' dC dC' aR aC) := by
  classical
  unfold archimedeanPairEpsilonProduct
  refine (continuous_finsetProd _ (fun v _ => ?_)).mul
    (continuous_finsetProd _ (fun v _ => ?_))
  · exact (differentiable_realEpsilon (realPairBlocks (dR v) (dR' v)) (aR v)
      (NNReal.sqrt ‖(aR v : ℝ)‖₊) (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr (aR v).ne_zero))).continuous
  · exact (differentiable_complexEpsilon (complexPairBlocks (dC v) (dC' v)) (aC v)
      ‖(aC v : ℂ)‖₊ (nnnorm_pos.mpr (aC v).ne_zero)).continuous

private theorem norm_archimedeanPairEpsilonProduct_eq
    (dR dR' : {v : InfinitePlace F // v.IsReal} → List RealBlock)
    (dC dC' : {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData)
    (aR : {v : InfinitePlace F // v.IsReal} → ℝˣ)
    (aC : {v : InfinitePlace F // v.IsComplex} → ℂˣ)
    {s t : ℂ} (h : s.re = t.re) :
    ‖archimedeanPairEpsilonProduct dR dR' dC dC' aR aC s‖ =
      ‖archimedeanPairEpsilonProduct dR dR' dC dC' aR aC t‖ := by
  classical
  simp only [archimedeanPairEpsilonProduct, norm_mul, norm_prod]
  congr 1
  · refine Finset.prod_congr rfl (fun v _ => ?_)
    simp only [realPairEpsilon, coe_realEpsilon, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr (aR v).ne_zero),
      Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero,
      Complex.sub_re, Complex.one_re, h]
  · refine Finset.prod_congr rfl (fun v _ => ?_)
    simp only [complexPairEpsilon, coe_complexEpsilon, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.mpr (aC v).ne_zero),
      Complex.mul_re, Complex.natCast_re, Complex.natCast_im, Complex.re_ofNat, Complex.im_ofNat,
      Complex.mul_im, zero_mul, mul_zero, sub_zero, add_zero,
      Complex.sub_re, Complex.one_re, h]

section FiniteData

variable [CompactSpace (AdeleQuotient F)]
  {r t : ℕ} {T Td : CuspidalOperatorRealization F r} {T' Td' : CuspidalOperatorRealization F t}
  {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}
  {P : CuspidalSpectralPresentation.{u, uQ} T} {P' : CuspidalSpectralPresentation.{u, uQ} T'}
  {Pd : CuspidalSpectralPresentation.{u, uQ} Td} {Pd' : CuspidalSpectralPresentation.{u, uQ} Td'}
  {h : HasIrreducibleAdmissibleComponents P} {h' : HasIrreducibleAdmissibleComponents P'}
  {hd : HasIrreducibleAdmissibleComponents Pd} {hd' : HasIrreducibleAdmissibleComponents Pd'}

private theorem continuous_finiteEpsilon (c : FinitePairFactorChoice ψ P P' Pd Pd' h h' hd hd')
    (v : FinitePlace F) : Continuous (c.finiteEpsilon v) := by
  have hpos : 0 < residueCardinality v := zero_lt_two.trans_le (two_le_residueCardinality v)
  have hq : (residueCardinality v : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hpt : Continuous (fun s => RankinSelberg.spectralPoint (residueCardinality v) s) :=
    continuous_neg.const_cpow (.inl hq)
  exact continuous_const.mul (hpt.zpow₀ _ (fun s =>
    .inl (RankinSelberg.spectralPoint_ne_zero_of_pos hpos s)))

private theorem norm_finiteEpsilon_eq (c : FinitePairFactorChoice ψ P P' Pd Pd' h h' hd hd')
    (v : FinitePlace F) {s t : ℂ} (he : s.re = t.re) :
    ‖c.finiteEpsilon v s‖ = ‖c.finiteEpsilon v t‖ := by
  simp only [FinitePairFactorChoice.finiteEpsilon, norm_mul, norm_zpow, norm_spectralPoint, he]

/-- The completed functional equation supplies left boundary lines for any
continuation of the specified completed Euler product with the simple-pole profile.
The finite factors in the equation and in the continuation may be different
certified choices for the same local components. -/
theorem hasLeftVerticalLineBounds_of_completedEquation
    (c : FinitePairLChoice P P' h h')
    (e : FinitePairFactorChoice ψ P P' Pd Pd' h h' hd hd')
    (S : Finset (FinitePlace F))
    (dR dR' dRd dRd' : {v : InfinitePlace F // v.IsReal} → List RealBlock)
    (dC dC' dCd dCd' : {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData)
    (aR : {v : InfinitePlace F // v.IsReal} → ℝˣ)
    (aC : {v : InfinitePlace F // v.IsComplex} → ℂˣ)
    {Λ : ℂ → ℂ} {cond : Prop}
    (hΛ : HasSimplePoleProfile Λ cond)
    (hL : c.IsCompletedLFunction (archimedeanPairProduct dR dR' dC dC') Λ)
    (hEq : e.CompletedEquationHolds S (archimedeanPairProduct dR dR' dC dC')
      (archimedeanPairProduct dRd dRd' dCd dCd')
      (archimedeanPairEpsilonProduct dR dR' dC dC' aR aC)) :
    HasLeftVerticalLineBounds Λ := by
  classical
  let ed : FinitePairLChoice Pd Pd' hd hd' :=
    ⟨e.additive, e.measure, e.measure_spec, e.dualLPolynomial, e.dualLPolynomial_spec⟩
  let Ad := archimedeanPairProduct dRd dRd' dCd dCd'
  let Ea := archimedeanPairEpsilonProduct dR dR' dC dC' aR aC
  let E (s : ℂ) := (∏ v ∈ S, e.finiteEpsilon v s) * Ea s
  obtain ⟨σ, L, D, hLm, _, hmatch, hE⟩ := hEq
  have hDm : ed.IsCompletedLFunction Ad D := by
    refine ⟨σ, fun s hs => ?_⟩
    obtain ⟨_, hsum, _, q, _, hq, _, he⟩ := hmatch s hs
    exact ⟨hsum, q, hq, he⟩
  have hcmp (s : ℂ) (v : FinitePlace F) : c.finiteL v s = e.finiteL v s :=
    c.finiteL_eq_of_localClass_eq (FinitePairLChoice.ofFactorChoice e) v rfl rfl s
  have hΛm : MeromorphicOn Λ univ := by
    intro s _
    by_cases hs : s ∈ ({0, 1} : Set ℂ)
    · exact (hΛ.2 s hs).1
    · exact (analyticAt_of_poleProfile hΛ hs).meromorphicAt
  obtain ⟨τ, hτ⟩ := hL
  have heq : Λ =ᶠ[codiscrete ℂ] L := by
    apply eventuallyEq_codiscrete_of_eq_on_right hΛm hLm (a := max σ τ)
    intro s hs
    obtain ⟨_, p, hp, hΛs⟩ := hτ s ((le_max_right σ τ).trans_lt hs)
    obtain ⟨_, _, p', _, hp', _, hLs, _⟩ := hmatch s ((le_max_left σ τ).trans_lt hs)
    have hp₁ : HasProd (fun v => e.finiteL v s) p := hp.congr_fun (fun v => (hcmp s v).symm)
    rw [hΛs, hLs, hp₁.unique hp']
  obtain ⟨β, hβ⟩ := completedPairRightStripBounds F r t Td Td' Pd Pd' hd hd' ed
    dRd dRd' dCd dCd' D hDm
  obtain ⟨γ, hγ⟩ := exists_continuousOn_archimedeanPairProduct_mul dRd dRd' dCd dCd'
    ed.rightHalfPlaneContinuous
  have hDc : ContinuousOn D {s : ℂ | max (max σ β) γ < s.re} := by
    have hsub : {s : ℂ | max (max σ β) γ < s.re} ⊆ {s : ℂ | γ < s.re} :=
      fun _ hs => (le_max_right (max σ β) γ).trans_lt hs
    refine (hγ.mono hsub).congr (fun s hs => ?_)
    obtain ⟨_, _, _, q, _, hq, _, he⟩ := hmatch s
      (((le_max_left σ β).trans (le_max_left _ γ)).trans_lt hs)
    change D s = Ad s * (∏' v, ed.finiteL v s)
    have hq' : HasProd (fun v => ed.finiteL v s) q := hq
    rw [hq'.tprod_eq]
    exact he
  refine hasLeftVerticalLineBounds_of_equation hΛ (D := D) (E := E) ?_ ?_ hDc ?_ (heq.trans hE)
  · exact (continuous_finsetProd _ fun v _ => continuous_finiteEpsilon e v).mul
      (continuous_archimedeanPairEpsilonProduct dR dR' dC dC' aR aC)
  · intro s t he
    simp only [E, Ea, norm_mul, norm_prod, norm_archimedeanPairEpsilonProduct_eq dR dR' dC dC' aR aC he]
    rw [Finset.prod_congr rfl (fun v _ => norm_finiteEpsilon_eq e v he)]
  · intro b hb
    obtain ⟨C, hC, hCb⟩ := hβ b b (((le_max_right σ β).trans (le_max_left _ γ)).trans_lt hb)
    exact ⟨C, hC, fun s hs => hCb s hs.ge hs.le⟩

end FiniteData

end Langlands.Global.CuspidalPairPoles
