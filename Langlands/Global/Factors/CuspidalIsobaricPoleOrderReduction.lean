import Langlands.Global.Factors.CuspidalIsobaricPoleOrderStatement
import Langlands.Global.Factors.CuspidalPairBoundaryNonvanishingStatement
import Langlands.Global.Factors.CuspidalPairFiniteLayer
import Langlands.Global.Factors.CuspidalPairResidueCardinality
import Langlands.Global.Factors.CuspidalSplitCentreUnitaryProof
import Langlands.Global.Factors.FiniteComparisonProof
import Langlands.Automorphic.ContragredientSymmetry
import Langlands.Correspondence.AutomorphicGammaGerm
import Mathlib.Algebra.BigOperators.WithTop

/-! # Reduction of the cuspidal-isobaric pole order to the pair theorems -/

noncomputable section

set_option autoImplicit false

open scoped BigOperators Topology

universe u uQ

namespace Langlands.Global

open NumberField
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation OperatorRealization)
open CompletionPadic CuspidalPairBoundaryNonvanishing CuspidalPairFunctionalEquation
open CuspidalPairFunctionalEquation.FinitePairFactorChoice (one_lt_residueCardinality)
open CuspidalPairPoles CuspidalIsobaricPoles LocalFactor.Archimedean

namespace CuspidalIsobaricPoles

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

private theorem contragredient_iff {r t : ℕ} (T : CuspidalOperatorRealization F r)
    (T' : CuspidalOperatorRealization F t) :
    (∃ hrt : r = t, OperatorRealization.IsContragredientOf (n := t + 1)
      (hrt ▸ T.realization) T'.realization) ↔
    (∃ hrt : r = t, OperatorRealization.IsContragredientOf (n := t + 1)
      T'.realization (hrt ▸ T.realization)) := by
  constructor <;> rintro ⟨hrt, h⟩ <;> subst t <;>
    exact ⟨rfl, Automorphic.CuspidalOperatorRealization.isContragredientOf_symm h⟩

private theorem meromorphicOn_of_poleProfile {Λ : ℂ → ℂ} {cond : Prop}
    (h : HasSimplePoleProfile Λ cond) : MeromorphicOn Λ Set.univ := by
  have hopen : IsOpen ({0, 1} : Set ℂ)ᶜ :=
    ((Set.finite_singleton (1 : ℂ)).insert 0).isClosed.isOpen_compl
  intro z _
  by_cases hz : z ∈ ({0, 1} : Set ℂ)
  · exact (h.2 z hz).1
  · exact (h.1.analyticAt (hopen.mem_nhds hz)).meromorphicAt

variable {r t : ℕ} {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
  {P : CuspidalSpectralPresentation.{u, uQ} T} {P' : CuspidalSpectralPresentation.{u, uQ} T'}
  {h : HasIrreducibleAdmissibleComponents P} {h' : HasIrreducibleAdmissibleComponents P'}

private theorem completed_order_eq (c : FinitePairLChoice P P' h h') {Linf Λ Λ' : ℂ → ℂ}
    (hΛ : MeromorphicOn Λ Set.univ) (hΛ' : MeromorphicOn Λ' Set.univ)
    (hc : c.IsCompletedLFunction Linf Λ) (hc' : c.IsCompletedLFunction Linf Λ') (z : ℂ) :
    meromorphicOrderAt Λ z = meromorphicOrderAt Λ' z := by
  obtain ⟨σ, hσ⟩ := hc
  obtain ⟨σ', hσ'⟩ := hc'
  apply meromorphicOrderAt_congr
  apply FunctionalEquationComparison.eq_on_halfplane_meromorphicEq
    (σ := max σ σ') (meromorphicOn_univ.mp hΛ) (meromorphicOn_univ.mp hΛ') _ z
  intro s hs
  obtain ⟨-, p, hp, hval⟩ := hσ s ((le_max_left _ _).trans_lt hs)
  obtain ⟨-, p', hp', hval'⟩ := hσ' s ((le_max_right _ _).trans_lt hs)
  rw [hval, hval', hp.unique hp']

private def finiteDenominator (c : FinitePairLChoice P P' h h') (v : FinitePlace F) :
    LocalFactor.ReciprocalEntire where
  denominator := fun s => (c.lPolynomial v).eval (RankinSelberg.spectralPoint (residueCardinality v) s)
  entire := fun s => (RankinSelberg.analyticAt_polynomial_spectralPoint _
    (one_lt_residueCardinality v) (c.lPolynomial v) s).differentiableAt
  nonzero := (RankinSelberg.polynomial_spectralPoint_eventually_ne_zero _
    (one_lt_residueCardinality v) (c.lPolynomial v) (c.lPolynomial_spec v).ne_zero 1).exists

private theorem reciprocal_order_nonpos (D : LocalFactor.ReciprocalEntire) (z : ℂ) :
    meromorphicOrderAt (fun s => (D.denominator s)⁻¹) z ≤ 0 := by
  have ha := D.entire.analyticAt z
  have hfinite := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero ha.meromorphicAt).mpr
    (D.denominator_eventually_ne_zero z)
  have hnonneg := ha.meromorphicOrderAt_nonneg
  change meromorphicOrderAt D.denominator⁻¹ z ≤ 0
  rw [meromorphicOrderAt_inv]
  lift meromorphicOrderAt D.denominator z to ℤ using hfinite with n
  exact_mod_cast neg_nonpos.mpr (show (0 : ℤ) ≤ n by exact_mod_cast hnonneg)

private theorem reciprocalProduct_properties {ι : Type*} (S : Finset ι)
    (D : ι → LocalFactor.ReciprocalEntire) (z : ℂ) :
    Meromorphic (fun s => ∏ v ∈ S, ((D v).denominator s)⁻¹) ∧
    meromorphicOrderAt (fun s => ∏ v ∈ S, ((D v).denominator s)⁻¹) z ≤ 0 := by
  have hmer (v : ι) (s : ℂ) : MeromorphicAt (fun w => ((D v).denominator w)⁻¹) s :=
    ((D v).entire.analyticAt s).meromorphicAt.inv
  refine ⟨fun s => MeromorphicAt.fun_prod (fun v _ => hmer v s), ?_⟩
  rw [meromorphicOrderAt_fun_prod (fun v _ => hmer v z)]
  exact Finset.sum_nonpos (fun v _ => reciprocal_order_nonpos (D v) z)

private theorem finiteL_eq_partialEulerFactor (c : FinitePairLChoice P P' h h')
    {S : Finset (FinitePlace F)} (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
    (v : {v : FinitePlace F // v ∉ S}) (s : ℂ) :
    c.finiteL v.1 s = partialEulerFactor P P' hP hP' v s := by
  unfold FinitePairLChoice.finiteL partialEulerFactor
  rw [isAutomorphicPairLPolynomial_eq_pairEulerPolynomial (padicField v.1) (c.additive v.1)
    (c.measure_spec v.1) _ _ (hasSphericalSpectrum_padicObject P h v.1 (fun hv => v.2 (hP hv)))
    (hasSphericalSpectrum_padicObject P' h' v.1 (fun hv => v.2 (hP' hv)))
    (c.lPolynomial_spec v.1)]

private theorem completed_order_nonpos
    {S : Finset (FinitePlace F)} (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
    {L : ℂ → ℂ} (hL : IsPartialPairLFunction P P' hP hP' L)
    (hLorder : meromorphicOrderAt L 1 ≤ 0)
    (c : FinitePairLChoice P P' h h') {Linf Λ : ℂ → ℂ} (hinf : Meromorphic Linf)
    (hinfOrder : meromorphicOrderAt Linf 1 ≤ 0) (hΛ : MeromorphicOn Λ Set.univ)
    (hc : c.IsCompletedLFunction Linf Λ) : meromorphicOrderAt Λ 1 ≤ 0 := by
  classical
  let Lfinite (s : ℂ) := ∏ v ∈ S, c.finiteL v s
  have hfinite : Meromorphic Lfinite ∧ meromorphicOrderAt Lfinite 1 ≤ 0 :=
    reciprocalProduct_properties S (finiteDenominator c) 1
  have hprod : Meromorphic (fun s => Linf s * (Lfinite s * L s)) :=
    hinf.mul (hfinite.1.mul (meromorphicOn_univ.mp hL.1))
  obtain ⟨σ, hσ⟩ := hc
  obtain ⟨τ, hτ⟩ := hL.2
  have heq := FunctionalEquationComparison.eq_on_halfplane_meromorphicEq
    (σ := max σ τ) (meromorphicOn_univ.mp hΛ) hprod (fun s hs => by
      obtain ⟨-, p, hp, hΛs⟩ := hσ s ((le_max_left _ _).trans_lt hs)
      have htail : HasProd (fun v : {v : FinitePlace F // v ∉ S} => c.finiteL v.1 s) (L s) :=
        (hτ s ((le_max_right _ _).trans_lt hs)).2.congr_fun
          (fun v => finiteL_eq_partialEulerFactor c hP hP' v s)
      have hall := (S.hasProd (fun v => c.finiteL v s)).mul_compl htail
      rw [hΛs, hp.unique hall])
  rw [meromorphicOrderAt_congr (heq 1)]
  change meromorphicOrderAt (Linf * (Lfinite * L)) 1 ≤ 0
  have hLmer := meromorphicOn_univ.mp hL.1
  rw [meromorphicOrderAt_mul (hinf 1) ((hfinite.1 1).mul (hLmer 1)),
    meromorphicOrderAt_mul (hfinite.1 1) (hLmer 1)]
  exact add_nonpos hinfOrder (add_nonpos hfinite.2 hLorder)

private theorem poleOrder_of_factorOrders {k : ℕ} (p : Fin k → Prop) (Λ : Fin k → ℂ → ℂ)
    (hmer : ∀ i, MeromorphicAt (Λ i) 1)
    (hlower : ∀ i, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (Λ i) 1)
    (hupper : ∀ i, meromorphicOrderAt (Λ i) 1 ≤ 0)
    (hpole : ∀ i, meromorphicOrderAt (Λ i) 1 < 0 ↔ p i) :
    HasPoleOrder (fun s => ∏ i, Λ i s) 1 (Nat.card {i : Fin k // p i}) := by
  classical
  let contribution (i : Fin k) : ℤ := if p i then -1 else 0
  have horder (i : Fin k) :
      meromorphicOrderAt (Λ i) 1 = (contribution i : WithTop ℤ) := by
    by_cases hi : p i
    · have hlt := (hpole i).mpr hi
      have hlo := hlower i
      have hfinite := ne_of_lt (hlt.trans (by simp : (0 : WithTop ℤ) < ⊤))
      lift meromorphicOrderAt (Λ i) 1 to ℤ using hfinite with n
      have hlow : (-1 : ℤ) ≤ n := WithTop.coe_le_coe.mp (by
        simpa only [WithTop.LinearOrderedAddCommGroup.coe_neg, WithTop.coe_one] using hlo)
      have hneg : n < 0 := by exact_mod_cast hlt
      have hn : n = -1 := by omega
      simp [contribution, hi, hn]
    · simp only [contribution, hi]
      exact (hupper i).antisymm (le_of_not_gt ((hpole i).not.mpr hi))
  have hsum : (∑ i : Fin k, contribution i) = -(Nat.card {i : Fin k // p i} : ℤ) := by
    rw [show (∑ i, contribution i) = ∑ i : Fin k, if p i then (-1 : ℤ) else 0 from rfl,
      ← Finset.sum_filter]
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
  unfold HasPoleOrder
  rw [meromorphicOrderAt_fun_prod (fun i _ => hmer i), Finset.sum_congr rfl (fun i _ => horder i),
    ← WithTop.coe_sum, hsum, min_eq_left]
  exact_mod_cast neg_nonpos.mpr (Int.natCast_nonneg _)

/-- Each split-centre-trivial pair with irreducible admissible finite components
has a partial L-function of nonpositive order at `1`. -/
def PartialPairNonvanishingAtOne (F : Type u) [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] : Prop :=
  ∀ (r t : ℕ) (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t),
    IsTrivialOnSplitCentre T → IsTrivialOnSplitCentre T' →
    ∀ (P : CuspidalSpectralPresentation.{u, uQ} T) (P' : CuspidalSpectralPresentation.{u, uQ} T'),
      HasIrreducibleAdmissibleComponents P → HasIrreducibleAdmissibleComponents P' →
      ∀ (S : Finset (FinitePlace F)) (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S),
        ∃ L : ℂ → ℂ, IsPartialPairLFunction P P' hP hP' L ∧ meromorphicOrderAt L 1 ≤ 0

end CuspidalIsobaricPoles

/-- Assemble existence and the pole order using a partial pair representative
of nonpositive order at `1` for each pair. -/
theorem cuspidalIsobaricPoleOrder_of_partialPairNonvanishingAtOne
    (hPair : CuspidalPairPoleStatement.{u, uQ})
    (hPartial : ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)],
      PartialPairNonvanishingAtOne.{u, uQ} F) : CuspidalIsobaricPoleOrderStatement.{u, uQ} := by
  classical
  intro F _ _ _ r₀ T₀ k r T hT₀ hT P₀ P h₀ h
  have hself := hPair F r₀ r₀ T₀ T₀ hT₀ hT₀ P₀ P₀ h₀ h₀
  have hpair (i : Fin k) := hPair F r₀ (r i) T₀ (T i) hT₀ (hT i) P₀ (P i) h₀ (h i)
  refine ⟨⟨fun i => (hpair i).1.1,
    fun v => ⟨(hself.1.2.1 v).1, fun i => ((hpair i).1.2.1 v).2⟩,
    fun v => ⟨(hself.1.2.2 v).1, fun i => ((hpair i).1.2.2 v).2⟩⟩, ?_⟩
  intro c dR₀ dR hdR₀ hdR dC₀ dC hdC₀ hdC infiniteL IsPairLFunction
  let isDual (i : Fin k) := ∃ hrt : r₀ = r i,
    OperatorRealization.IsContragredientOf (n := r i + 1) (hrt ▸ T₀.realization) (T i).realization
  have hwitness (i : Fin k) : ∃ Λ, IsPairLFunction i Λ ∧ HasSimplePoleProfile Λ (isDual i) := by
    obtain ⟨Λ, hc, hprofile, -⟩ :=
      (hpair i).2 (c i) dR₀ (dR i) hdR₀ (hdR i) dC₀ (dC i) hdC₀ (hdC i)
    exact ⟨Λ, ⟨meromorphicOn_of_poleProfile hprofile, hc⟩, hprofile⟩
  choose Λ₀ hΛ₀ hpoles using hwitness
  refine ⟨⟨Λ₀, hΛ₀⟩, ?_⟩
  intro Λ hΛ
  have horder (i : Fin k) : meromorphicOrderAt (Λ i) 1 = meromorphicOrderAt (Λ₀ i) 1 :=
    completed_order_eq (c i) (hΛ i).1 (hΛ₀ i).1 (hΛ i).2 (hΛ₀ i).2 1
  have hprofile (i : Fin k) := (hpoles i).2 1 (by simp)
  apply poleOrder_of_factorOrders _ Λ (fun i => (hΛ i).1 1 (Set.mem_univ 1))
  · intro i
    rw [horder i]
    exact (hprofile i).2.1
  · intro i
    let realD v := realPairLFactor (dR₀ v) (dR i v)
    let complexD v := complexPairLFactor (dC₀ v) (dC i v)
    let realL (s : ℂ) := ∏ v, ((realD v).denominator s)⁻¹
    let complexL (s : ℂ) := ∏ v, ((complexD v).denominator s)⁻¹
    have hreal : Meromorphic realL ∧ meromorphicOrderAt realL 1 ≤ 0 :=
      reciprocalProduct_properties Finset.univ realD 1
    have hcomplex : Meromorphic complexL ∧ meromorphicOrderAt complexL 1 ≤ 0 :=
      reciprocalProduct_properties Finset.univ complexD 1
    let S := P₀.exceptional ∪ (P i).exceptional
    have hP₀ : P₀.exceptional ⊆ S := Finset.subset_union_left
    have hP : (P i).exceptional ⊆ S := Finset.subset_union_right
    obtain ⟨L, hL, hLorder⟩ :=
      hPartial F r₀ (r i) T₀ (T i) hT₀ (hT i) P₀ (P i) h₀ (h i) S hP₀ hP
    apply completed_order_nonpos hP₀ hP hL hLorder (c i) (hreal.1.mul hcomplex.1)
      _ (hΛ i).1 (hΛ i).2
    change meromorphicOrderAt (realL * complexL) 1 ≤ 0
    rw [meromorphicOrderAt_mul (hreal.1 1) (hcomplex.1 1)]
    exact add_nonpos hreal.2 hcomplex.2
  · intro i
    rw [horder i]
    exact (hprofile i).2.2.trans (contragredient_iff T₀ (T i))

/-- The pair-pole theorem and boundary nonvanishing imply the published isobaric pole order. -/
def CuspidalIsobaricPoleOrderReductionStatement : Prop :=
  CuspidalPairPoleStatement.{u, uQ} → CuspidalPairBoundaryNonvanishingStatement.{u, uQ} →
    CuspidalIsobaricPoleOrderStatement.{u, uQ}

/-- Assemble the existence and pole-order conclusions from the two analytic pair theorems. -/
theorem cuspidalIsobaricPoleOrderReduction : CuspidalIsobaricPoleOrderReductionStatement.{u, uQ} := by
  intro hPair hBoundary
  apply cuspidalIsobaricPoleOrder_of_partialPairNonvanishingAtOne hPair
  intro F _ _ _ r t T T' hT hT' P P' _ _ S hP hP'
  obtain ⟨⟨L, hL⟩, hBoundaryOrder⟩ := hBoundary F r t T T'
    (cuspidalSplitCentreUnitaryCentralCharacter F r T hT)
    (cuspidalSplitCentreUnitaryCentralCharacter F t T' hT') P P' S hP hP'
  exact ⟨L, hL, by simpa using hBoundaryOrder L hL 0⟩

end Langlands.Global
