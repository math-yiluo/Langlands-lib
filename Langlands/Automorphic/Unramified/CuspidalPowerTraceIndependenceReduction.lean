import Langlands.Automorphic.Unramified.CuspidalSpectralRigidityTCStatement
import Langlands.Automorphic.AssociatedPresentationSpectrum
import Langlands.Automorphic.RealizationEquivalenceTransport
import Langlands.Automorphic.CuspidalAdmissible.Existence
import Langlands.Automorphic.CuspidalPresentationUniverse
import Langlands.Automorphic.CuspidalSlicePresentation
import Langlands.Global.Factors.CuspidalNormPowerTwist
import Langlands.Global.Factors.CuspidalPairLogSeries

/-! # Cuspidal trace independence from logarithmic asymptotics

The proof implements Jacquet–Shalika II, Theorem 4.2, using the logarithmic
boundary limit of Theorem 4.1. It applies the argument over a single number field
and obtains the unrestricted and totally complex implications. -/

noncomputable section

set_option autoImplicit false

open scoped BigOperators Classical

universe uF uV

open Filter Topology

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Unramified
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents residueCardinality)
open CuspidalPairAbsoluteConvergence
open CuspidalPairPoles

namespace PowerTraceIndependence

variable {F : Type uF} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 4000000 in
/-- If, after a common Hecke twist `χ`, the conjugate of the first twist realizes the
contragredient of the second twist, while the second twist is unitary in the sense that its own
conjugate realizes its contragredient, then the two realizations are equivalent. -/
theorem isoClass_eq_of_isContragredientOf_twist {r : ℕ} (T₀ T₁ : CuspidalOperatorRealization F r)
    (χ : HeckeCharacter F)
    (h₁ : (T₁.heckeDeterminantTwist χ).conjugate.realization.IsContragredientOf
      (T₁.heckeDeterminantTwist χ).realization)
    (hC : (T₀.heckeDeterminantTwist χ).conjugate.realization.IsContragredientOf
      (T₁.heckeDeterminantTwist χ).realization) :
    T₀.isoClass = T₁.isoClass := by
  rw [CuspidalOperatorRealization.isoClass_eq_iff]
  obtain ⟨e⟩ := OperatorRealization.nonempty_equivalence_conjugate
    (OperatorRealization.IsContragredientOf.nonempty_equivalence hC h₁)
  obtain ⟨a⟩ := OperatorRealization.nonempty_equivalence_conjugate_conjugate
    (T₀.realization.heckeDeterminantTwist χ)
  obtain ⟨b⟩ := OperatorRealization.nonempty_equivalence_conjugate_conjugate
    (T₁.realization.heckeDeterminantTwist χ)
  have e3 : Nonempty ((T₀.realization.heckeDeterminantTwist χ).Equivalence
      (T₁.realization.heckeDeterminantTwist χ)) := ⟨a.trans (e.trans b.symm)⟩
  have e4 := OperatorRealization.nonempty_equivalence_heckeDeterminantTwist χ⁻¹ e3
  rw [OperatorRealization.heckeDeterminantTwist_heckeDeterminantTwist_inv,
    OperatorRealization.heckeDeterminantTwist_heckeDeterminantTwist_inv] at e4
  exact e4

/-- The mixed-rank form of `isoClass_eq_of_isContragredientOf_twist`. -/
theorem positiveRankClass_eq_of_isContragredientOf_twist {r r' : ℕ} (hrt : r = r')
    (T₀ : CuspidalOperatorRealization F r) (T₁ : CuspidalOperatorRealization F r')
    (χ : HeckeCharacter F)
    (h₁ : (T₁.heckeDeterminantTwist χ).conjugate.realization.IsContragredientOf
      (T₁.heckeDeterminantTwist χ).realization)
    (hC : OperatorRealization.IsContragredientOf (n := r' + 1)
      (hrt ▸ (T₀.heckeDeterminantTwist χ).conjugate.realization)
      (T₁.heckeDeterminantTwist χ).realization) :
    (⟨r, T₀.isoClass⟩ : PositiveRankCuspidalClass F) = ⟨r', T₁.isoClass⟩ := by
  subst hrt
  rw [isoClass_eq_of_isContragredientOf_twist T₀ T₁ χ h₁ hC]

/-- The traces of a presentation of `T` are those of any presentation of the twist
`T ⊗ ‖·‖^(-l)`, multiplied by `q_v^(-l k)`. -/
theorem powerTrace_eq_twist {r : ℕ} {T : CuspidalOperatorRealization F r}
    (P : CuspidalSpectralPresentation.{uF, uV} T) (l : ℂ)
    (Q : CuspidalSpectralPresentation.{uF, uV}
      (T.heckeDeterminantTwist (HeckeCharacter.normPower F (-l))))
    (v : FinitePlace F)
    (hv : v ∉ P.exceptional ∪ (HeckeCharacter.normPower F (-l)).finiteHeckeDeterminantTail (r + 1))
    (hvQ : v ∉ Q.exceptional) (k : ℕ) :
    P.spectralSystem.powerTrace v (fun h => hv (Finset.mem_union_left _ h)) k =
      ((residueCardinality v : ℂ) ^ (-l)) ^ k * Q.spectralSystem.powerTrace v hvQ k := by
  have h1 := P.heckeDeterminantTwist_powerTrace (HeckeCharacter.normPower F (-l)) v hv k
  rw [NormPowerTwist.finiteUniformizerValue_normPower, neg_neg] at h1
  have h2 : (P.heckeDeterminantTwist (HeckeCharacter.normPower F (-l))).spectralSystem.powerTrace
      v hv k = Q.spectralSystem.powerTrace v hvQ k := by
    unfold SpectralSystem.powerTrace
    rw [CuspidalSpectralPresentation.spectralSystem_eigenvalues_eq
      (P.heckeDeterminantTwist _) Q v hv hvQ]
  rw [h2] at h1
  have hq0 : (residueCardinality v : ℂ) ≠ 0 := by
    have := CuspidalPairEulerConvergence.two_le_residueCardinality v
    exact_mod_cast (show residueCardinality v ≠ 0 by omega)
  rw [h1, ← mul_assoc, ← mul_pow, ← Complex.cpow_add _ _ hq0, neg_add_cancel, Complex.cpow_zero,
    one_pow, one_mul]

/-- Equal systems have equal power traces, whatever the membership proofs. -/
theorem powerTrace_congr {ι : Type*} {n : ℕ} {σ τ : SpectralSystem ι n} (h : σ = τ) (v : ι)
    (hσ : v ∉ σ.exceptional) (hτ : v ∉ τ.exceptional) (k : ℕ) :
    σ.powerTrace v hσ k = τ.powerTrace v hτ k := by
  subst h
  rfl

set_option maxHeartbeats 4000000 in
/-- **The analytic core of Jacquet–Shalika II, Theorem (4.2).** Let `U_i` (`i ∈ I`) be unitary
cuspidal realizations trivial on the split centre, `Ud` another one, with presentations with
irreducible admissible components, and suppose that outside a finite set `S`

`∑_(i ∈ I) a_i q_v^(-k l_i) tr(A_(i,v)^k) = 0`  (`k ≥ 1`).

If `Re l_(i₀)` is minimal among the `Re l_i`, and among the `i ∈ I` exactly `i₀` has
`l_i = l_(i₀)` with `Ud` realizing the contragredient of `U_i`, then `a_(i₀) = 0`. The proof
multiplies the relation by `tr(Ad_v^k) q_v^(-k(σ - l_(i₀))) / k`, sums over `v` and `k`, and lets
`σ → 1⁺` after division by `log (1/(σ - 1))` (JS II, Theorem (4.1)). -/
theorem coeff_eq_zero_of_relation
    (hconv : CuspidalPairAbsoluteConvergenceStatement.{uF, uV})
    (hasymptotics : CuspidalPairLogAsymptoticsAt.{uF, uV} F)
    {ι : Type*} (I : Finset ι) {r₀ : ℕ} (Ud : CuspidalOperatorRealization F r₀)
    (hUd : Langlands.ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter Ud)
    (htd : IsTrivialOnSplitCentre Ud)
    (Qd : CuspidalSpectralPresentation.{uF, uV} Ud) (hQd : HasIrreducibleAdmissibleComponents Qd)
    (r : ι → ℕ) (U : ∀ i, CuspidalOperatorRealization F (r i))
    (hU : ∀ i, Langlands.ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter (U i))
    (ht : ∀ i, IsTrivialOnSplitCentre (U i))
    (Q : ∀ i, CuspidalSpectralPresentation.{uF, uV} (U i))
    (hQ : ∀ i, HasIrreducibleAdmissibleComponents (Q i))
    (S : Finset (FinitePlace F)) (hSd : Qd.exceptional ⊆ S) (hSQ : ∀ i, (Q i).exceptional ⊆ S)
    (l a : ι → ℂ)
    (hrel : ∀ (v : FinitePlace F) (hv : v ∉ S) (k : ℕ), 0 < k →
      ∑ i ∈ I, a i * (((residueCardinality v : ℂ) ^ (-l i)) ^ k *
        (Q i).spectralSystem.powerTrace v (fun h => hv (hSQ i h)) k) = 0)
    {i₀ : ι} (hi₀ : i₀ ∈ I) (hmin : ∀ i ∈ I, (l i₀).re ≤ (l i).re)
    (hcond : ∀ i ∈ I, ((l i = l i₀ ∧ ∃ hrt : r₀ = r i,
      OperatorRealization.IsContragredientOf (n := r i + 1) (hrt ▸ Ud.realization)
        (U i).realization) ↔ i = i₀)) :
    a i₀ = 0 := by
  classical
  set ser : ι → ℂ → ℂ := fun i z => ∑' x : {v : FinitePlace F // v ∉ S} × ℕ,
    logEulerTerm Qd (Q i) hSd (hSQ i) x.1 x.2 z with hser
  have hsum : ∀ i (z : ℂ), 1 < z.re → Summable fun x : {v : FinitePlace F // v ∉ S} × ℕ =>
      ‖logEulerTerm Qd (Q i) hSd (hSQ i) x.1 x.2 z‖ :=
    fun i z hz => (hconv F r₀ (r i) Ud (U i) hUd (hU i) Qd (Q i) S hSd (hSQ i) z hz).1
  -- the identity `∑ a_i l_i(σ + l_i - l_(i₀)) = 0`
  have hid : ∀ σ : ℝ, 1 < σ → ∑ i ∈ I, a i * ser i ((σ : ℂ) + (l i - l i₀)) = 0 := by
    intro σ hσ
    have hre : ∀ i ∈ I, 1 < ((σ : ℂ) + (l i - l i₀)).re := by
      intro i hi
      simp only [Complex.add_re, Complex.ofReal_re, Complex.sub_re]
      linarith [hmin i hi]
    have hterm : ∀ x : {v : FinitePlace F // v ∉ S} × ℕ,
        ∑ i ∈ I, a i * logEulerTerm Qd (Q i) hSd (hSQ i) x.1 x.2 ((σ : ℂ) + (l i - l i₀)) =
          0 := by
      intro x
      have hq0 : (residueCardinality x.1.1 : ℂ) ≠ 0 := by
        have := CuspidalPairEulerConvergence.two_le_residueCardinality x.1.1
        exact_mod_cast (show residueCardinality x.1.1 ≠ 0 by omega)
      have hsp : ∀ i, RankinSelberg.spectralPoint (residueCardinality x.1.1)
          ((σ : ℂ) + (l i - l i₀)) ^ (x.2 + 1) =
          RankinSelberg.spectralPoint (residueCardinality x.1.1) (σ : ℂ) ^ (x.2 + 1) *
            ((residueCardinality x.1.1 : ℂ) ^ (l i₀)) ^ (x.2 + 1) *
              ((residueCardinality x.1.1 : ℂ) ^ (-l i)) ^ (x.2 + 1) := by
        intro i
        unfold RankinSelberg.spectralPoint
        rw [← mul_pow, ← mul_pow, ← Complex.cpow_add _ _ hq0, ← Complex.cpow_add _ _ hq0]
        congr 2
        ring
      have h0 := hrel x.1.1 x.1.2 (x.2 + 1) (Nat.succ_pos _)
      calc ∑ i ∈ I, a i * logEulerTerm Qd (Q i) hSd (hSQ i) x.1 x.2 ((σ : ℂ) + (l i - l i₀))
          = (Qd.spectralSystem.powerTrace x.1.1 (fun h => x.1.2 (hSd h)) (x.2 + 1) *
              RankinSelberg.spectralPoint (residueCardinality x.1.1) (σ : ℂ) ^ (x.2 + 1) *
                ((residueCardinality x.1.1 : ℂ) ^ (l i₀)) ^ (x.2 + 1) / ((x.2 : ℂ) + 1)) *
            ∑ i ∈ I, a i * (((residueCardinality x.1.1 : ℂ) ^ (-l i)) ^ (x.2 + 1) *
              (Q i).spectralSystem.powerTrace x.1.1 (fun h => x.1.2 (hSQ i h)) (x.2 + 1)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            unfold logEulerTerm
            rw [hsp i]
            ring
        _ = 0 := by rw [h0, mul_zero]
    have hS : ∀ i ∈ I, Summable fun x : {v : FinitePlace F // v ∉ S} × ℕ =>
        a i * logEulerTerm Qd (Q i) hSd (hSQ i) x.1 x.2 ((σ : ℂ) + (l i - l i₀)) :=
      fun i hi => ((hsum i _ (hre i hi)).of_norm).mul_left (a i)
    calc ∑ i ∈ I, a i * ser i ((σ : ℂ) + (l i - l i₀))
        = ∑ i ∈ I, ∑' x : {v : FinitePlace F // v ∉ S} × ℕ,
            a i * logEulerTerm Qd (Q i) hSd (hSQ i) x.1 x.2 ((σ : ℂ) + (l i - l i₀)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hser, tsum_mul_left]
      _ = ∑' x : {v : FinitePlace F // v ∉ S} × ℕ, ∑ i ∈ I,
            a i * logEulerTerm Qd (Q i) hSd (hSQ i) x.1 x.2 ((σ : ℂ) + (l i - l i₀)) :=
          (Summable.tsum_finsetSum hS).symm
      _ = 0 := by simp only [hterm, tsum_zero]
  -- the limits of the individual terms
  have hlog : Tendsto (fun σ : ℝ => (Real.log (1 / (σ - 1)))⁻¹) (𝓝[>] 1) (𝓝 0) :=
    tendsto_inv_atTop_zero.comp PairLogAsymptotics.tendsto_log_inv_sub_one
  have hlogpos : ∀ σ : ℝ, 1 < σ → σ < 2 → 0 < Real.log (1 / (σ - 1)) := by
    intro σ h1 h2
    apply Real.log_pos
    rw [lt_div_iff₀ (sub_pos.mpr h1)]
    linarith
  have hlim : ∀ i ∈ I, Tendsto (fun σ : ℝ => ser i ((σ : ℂ) + (l i - l i₀)) /
      (Real.log (1 / (σ - 1)) : ℂ)) (𝓝[>] 1) (𝓝 (if i = i₀ then 1 else 0)) := by
    intro i hi
    rcases (hmin i hi).lt_or_eq with hlt | heq
    · have hne : i ≠ i₀ := by
        rintro rfl
        exact lt_irrefl _ hlt
      rw [show (if i = i₀ then (1 : ℂ) else 0) = 0 by simp [hne]]
      obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (l i).re - (l i₀).re := ⟨_, rfl⟩
      have hδ0 : 0 < δ := by rw [hδ]; exact sub_pos.mpr hlt
      have hs1 := hsum i (((1 + δ : ℝ)) : ℂ) (by rw [Complex.ofReal_re]; linarith)
      obtain ⟨C, hC⟩ : ∃ C : ℝ, C = ∑' x : {v : FinitePlace F // v ∉ S} × ℕ,
          ‖logEulerTerm Qd (Q i) hSd (hSQ i) x.1 x.2 (((1 + δ : ℝ)) : ℂ)‖ := ⟨_, rfl⟩
      have hreσ : ∀ σ : ℝ, ((σ : ℂ) + (l i - l i₀)).re = σ + δ := by
        intro σ
        simp only [Complex.add_re, Complex.ofReal_re, Complex.sub_re, hδ]
      have hbound : ∀ σ : ℝ, 1 < σ → ‖ser i ((σ : ℂ) + (l i - l i₀))‖ ≤ C := by
        intro σ hσ
        have hsσ := hsum i ((σ : ℂ) + (l i - l i₀)) (by rw [hreσ]; linarith)
        refine (norm_tsum_le_tsum_norm hsσ).trans ?_
        rw [hC]
        exact Summable.tsum_le_tsum (fun x => PairLogAsymptotics.norm_logEulerTerm_le_of_le_re
          Qd (Q i) hSd (hSQ i) x (by rw [hreσ]; linarith)) hsσ hs1
      have hlogC : Tendsto (fun σ : ℝ => C * (Real.log (1 / (σ - 1)))⁻¹) (𝓝[>] 1) (𝓝 0) := by
        have := hlog.const_mul C
        rwa [mul_zero] at this
      refine squeeze_zero_norm' ?_ hlogC
      filter_upwards [Ioo_mem_nhdsGT one_lt_two] with σ hσ
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hlogpos σ hσ.1 hσ.2),
        div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hbound σ hσ.1) (inv_nonneg.mpr (hlogpos σ hσ.1 hσ.2).le)
    · obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (l i - l i₀).im := ⟨_, rfl⟩
      have hshift : ∀ σ : ℝ, (σ : ℂ) + (l i - l i₀) = (σ : ℂ) + θ * Complex.I := by
        intro σ
        apply Complex.ext
        · simp [heq]
        · simp [hθ]
      have hfun : (fun σ : ℝ => ser i ((σ : ℂ) + (l i - l i₀)) /
          (Real.log (1 / (σ - 1)) : ℂ)) =
          fun σ : ℝ => (∑' x : {v : FinitePlace F // v ∉ S} × ℕ,
            logEulerTerm Qd (Q i) hSd (hSQ i) x.1 x.2 ((σ : ℂ) + θ * Complex.I)) /
              (Real.log (1 / (σ - 1)) : ℂ) := by
        funext σ
        show (∑' x : {v : FinitePlace F // v ∉ S} × ℕ,
            logEulerTerm Qd (Q i) hSd (hSQ i) x.1 x.2 ((σ : ℂ) + (l i - l i₀))) / _ = _
        rw [hshift]
      rw [hfun]
      obtain ⟨hpos, hzero⟩ := hasymptotics r₀ (r i) Ud (U i) hUd (hU i) htd (ht i)
        Qd (Q i) hQd (hQ i) S hSd (hSQ i) θ
      have hll : θ = 0 → l i = l i₀ := by
        intro h0
        apply Complex.ext
        · exact heq.symm
        · have h1 : (l i - l i₀).im = 0 := hθ ▸ h0
          simp only [Complex.sub_im] at h1
          linarith
      by_cases hii : i = i₀
      · rw [show (if i = i₀ then (1 : ℂ) else 0) = 1 by simp [hii]]
        obtain ⟨-, hc⟩ := (hcond i hi).mpr hii
        refine hpos ⟨?_, hc⟩
        rw [hθ, hii, sub_self, Complex.zero_im]
      · rw [show (if i = i₀ then (1 : ℂ) else 0) = 0 by simp [hii]]
        refine hzero ?_
        rintro ⟨h0, hc⟩
        exact hii ((hcond i hi).mp ⟨hll h0, hc⟩)
  -- the conclusion
  have hT := tendsto_finsetSum I fun i hi => (hlim i hi).const_mul (a i)
  have hval : ∑ i ∈ I, a i * (if i = i₀ then (1 : ℂ) else 0) = a i₀ := by
    simp [mul_ite, Finset.sum_ite_eq', hi₀]
  rw [hval] at hT
  have hz : (fun σ : ℝ => ∑ i ∈ I, a i * (ser i ((σ : ℂ) + (l i - l i₀)) /
      (Real.log (1 / (σ - 1)) : ℂ))) =ᶠ[𝓝[>] 1] fun _ => 0 := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have h1 : ∑ i ∈ I, a i * (ser i ((σ : ℂ) + (l i - l i₀)) / (Real.log (1 / (σ - 1)) : ℂ)) =
        (∑ i ∈ I, a i * ser i ((σ : ℂ) + (l i - l i₀))) / (Real.log (1 / (σ - 1)) : ℂ) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [h1, hid σ hσ, zero_div]
  exact tendsto_nhds_unique hT (tendsto_const_nhds.congr' hz.symm)

end PowerTraceIndependence

open PowerTraceIndependence

/-- An auxiliary presentation with all finite factors irreducible and admissible.
The irreducible admissible finite slice gives an initial factorization, then
`exists_small` puts the factors in the requested universe. -/
private theorem exists_irreducibleAdmissible_presentation {F : Type uF} [Field F]
    [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
    (T : CuspidalOperatorRealization F r) :
    ∃ Q : CuspidalSpectralPresentation.{uF, uV} T, HasIrreducibleAdmissibleComponents Q := by
  obtain ⟨A, hI, hA⟩ := Automorphic.cuspidalIrreducibleAdmissibleFiniteSliceExistence F r T
  obtain ⟨P, hP⟩ := T.exists_presentation_of_finiteSlice A hI hA
  exact P.exists_small hP

set_option maxHeartbeats 4000000 in
/-- Jacquet–Shalika II, Theorem 4.2, over one number field. -/
theorem cuspidalPowerTraceIndependenceAt_of_pairLogAsymptotics {F : Type uF} [Field F]
    [NumberField F] [CompactSpace (AdeleQuotient F)]
    (hconv : CuspidalPairAbsoluteConvergenceStatement.{uF, uV})
    (hasymptotics : CuspidalPairLogAsymptoticsAt.{uF, uV} F) :
    ∀ (p : ℕ) (c : Fin p → PositiveRankCuspidalClass F)
      (s : ∀ i, SpectralSystem (FinitePlace F) (c i).rank),
      (∀ i, PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} (c i) (s i)) →
      Function.Injective c →
      ∀ (S : Finset (FinitePlace F)) (hS : ∀ i, (s i).exceptional ⊆ S)
        (a : Fin p → ℂ),
        (∀ (v : FinitePlace F) (hv : v ∉ S) (k : ℕ), 0 < k →
          (∑ i, a i * (s i).powerTrace v (fun h => hv (hS i h)) k) = 0) →
        ∀ i, a i = 0 := by
  classical
  intro p c s hs hinj S hS a hrel
  -- representatives, twists and auxiliary presentations
  have hrep : ∀ i, ∃ (T : CuspidalOperatorRealization F (c i).1)
      (P : CuspidalSpectralPresentation.{uF, uV} T), T.isoClass = (c i).2 ∧
        P.spectralSystem = s i := fun i => hs i
  choose T P hTc hPs using hrep
  choose l hl using fun i => NormPowerTwist.exists_normPower_twist (T i)
  choose Q hQ using fun i => exists_irreducibleAdmissible_presentation.{uF, uV}
    ((T i).heckeDeterminantTwist (HeckeCharacter.normPower F (-(l i))))
  choose Qd hQd using fun i =>
    exists_irreducibleAdmissible_presentation.{uF, uV}
      ((T i).heckeDeterminantTwist (HeckeCharacter.normPower F (-(l i)))).conjugate
  -- the enlarged exceptional set
  set tail : Fin p → Finset (FinitePlace F) := fun i =>
    (HeckeCharacter.normPower F (-(l i))).finiteHeckeDeterminantTail ((c i).1 + 1) with htail
  set S' : Finset (FinitePlace F) := S ∪ Finset.univ.biUnion (fun i =>
    (P i).exceptional ∪ tail i ∪ (Q i).exceptional ∪ (Qd i).exceptional) with hS'
  have hmemS' : ∀ i, (P i).exceptional ∪ tail i ∪ (Q i).exceptional ∪ (Qd i).exceptional ⊆ S' :=
    fun i x hx => by
      rw [hS', Finset.mem_union, Finset.mem_biUnion]
      exact Or.inr ⟨i, Finset.mem_univ _, hx⟩
  have hSS' : S ⊆ S' := fun x hx => by
    rw [hS', Finset.mem_union]
    exact Or.inl hx
  have hPS' : ∀ i, (P i).exceptional ∪ tail i ⊆ S' := fun i =>
    (Finset.subset_union_left.trans Finset.subset_union_left).trans (hmemS' i)
  have hQS' : ∀ i, (Q i).exceptional ⊆ S' := fun i =>
    (Finset.subset_union_right.trans Finset.subset_union_left).trans (hmemS' i)
  have hQdS' : ∀ i, (Qd i).exceptional ⊆ S' := fun i =>
    Finset.subset_union_right.trans (hmemS' i)
  -- the relation for the auxiliary presentations of the twists
  have hrel' : ∀ (v : FinitePlace F) (hv : v ∉ S') (k : ℕ), 0 < k →
      ∑ i, a i * (((residueCardinality v : ℂ) ^ (-l i)) ^ k *
        (Q i).spectralSystem.powerTrace v (fun h => hv (hQS' i h)) k) = 0 := by
    intro v hv k hk
    rw [← hrel v (fun h => hv (hSS' h)) k hk]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [powerTrace_congr (hPs i).symm v _ (fun h => hv (hPS' i (Finset.mem_union_left _ h))) k]
    exact (powerTrace_eq_twist (P i) (l i) (Q i) v (fun h => hv (hPS' i h))
      (fun h => hv (hQS' i h)) k).symm
  -- reduction to the support of the coefficients
  by_contra hne
  simp only [not_forall] at hne
  set I : Finset (Fin p) := Finset.univ.filter (fun i => a i ≠ 0) with hI
  have hIne : I.Nonempty := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  obtain ⟨i₀, hi₀, hmin⟩ := I.exists_min_image (fun i => (l i).re) hIne
  have hrelI : ∀ (v : FinitePlace F) (hv : v ∉ S') (k : ℕ), 0 < k →
      ∑ i ∈ I, a i * (((residueCardinality v : ℂ) ^ (-l i)) ^ k *
        (Q i).spectralSystem.powerTrace v (fun h => hv (hQS' i h)) k) = 0 := by
    intro v hv k hk
    rw [← hrel' v hv k hk]
    refine Finset.sum_subset (Finset.subset_univ I) fun i _ hi => ?_
    have hai : a i = 0 := by
      by_contra h
      exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    rw [hai, zero_mul]
  have hcond : ∀ i ∈ I, ((l i = l i₀ ∧ ∃ hrt : (c i₀).1 = (c i).1,
      Automorphic.OperatorRealization.IsContragredientOf (n := (c i).1 + 1)
        (hrt ▸ ((T i₀).heckeDeterminantTwist
          (HeckeCharacter.normPower F (-(l i₀)))).conjugate.realization)
        ((T i).heckeDeterminantTwist (HeckeCharacter.normPower F (-(l i)))).realization) ↔
      i = i₀) := by
    intro i _
    constructor
    · rintro ⟨hll, hrt, hC⟩
      rw [← hll] at hC
      have heq := positiveRankClass_eq_of_isContragredientOf_twist hrt (T i₀) (T i)
        (HeckeCharacter.normPower F (-(l i))) (hl i).2.2.2.2 hC
      rw [hTc i₀, hTc i] at heq
      exact (hinj (heq : c i₀ = c i)).symm
    · rintro rfl
      exact ⟨rfl, rfl, (hl i).2.2.2.2⟩
  have key := coeff_eq_zero_of_relation hconv hasymptotics I
    ((T i₀).heckeDeterminantTwist (HeckeCharacter.normPower F (-(l i₀)))).conjugate
    (hl i₀).2.2.2.1 (hl i₀).2.2.1 (Qd i₀) (hQd i₀) (fun i => (c i).1)
    (fun i => (T i).heckeDeterminantTwist (HeckeCharacter.normPower F (-(l i))))
    (fun i => (hl i).1) (fun i => (hl i).2.1) Q hQ S' (hQdS' i₀) hQS' l a hrelI hi₀
    hmin hcond
  exact (Finset.mem_filter.mp hi₀).2 key

/-- Trace independence from the logarithmic boundary limit for every number field. -/
theorem cuspidalPowerTraceIndependence_of_pairLogAsymptotics
    (hconv : CuspidalPairAbsoluteConvergenceStatement.{uF, uV})
    (hasymptotics : ∀ (F : Type uF) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)],
      CuspidalPairLogAsymptoticsAt.{uF, uV} F) :
    CuspidalPowerTraceIndependenceStatement.{uF, uV} := fun F _ _ _ =>
  cuspidalPowerTraceIndependenceAt_of_pairLogAsymptotics hconv (hasymptotics F)

/-- The same implication over totally complex number fields. -/
theorem cuspidalPowerTraceIndependenceTC_of_pairLogAsymptotics
    (hconv : CuspidalPairAbsoluteConvergenceStatement.{uF, uV})
    (hasymptotics : ∀ (F : Type uF) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
        [CompactSpace (AdeleQuotient F)], CuspidalPairLogAsymptoticsAt.{uF, uV} F) :
    CuspidalPowerTraceIndependenceTCStatement.{uF, uV} := fun F _ _ _ _ =>
  cuspidalPowerTraceIndependenceAt_of_pairLogAsymptotics hconv (hasymptotics F)

/-- Jacquet–Shalika II, Theorem 4.2, follows from absolute convergence and the
boundary limit of Theorem 4.1. The latter need only hold over totally complex
fields for the totally complex conclusion. -/
def CuspidalPowerTraceIndependenceReductionStatement : Prop :=
  CuspidalPairAbsoluteConvergenceStatement.{uF, uV} →
    (((∀ (F : Type uF) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)],
        CuspidalPairLogAsymptoticsAt.{uF, uV} F) →
      CuspidalPowerTraceIndependenceStatement.{uF, uV}) ∧
    ((∀ (F : Type uF) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
        [CompactSpace (AdeleQuotient F)], CuspidalPairLogAsymptoticsAt.{uF, uV} F) →
      CuspidalPowerTraceIndependenceTCStatement.{uF, uV}))

/-- The two implications, each using the logarithmic asymptotic only over
the number field of the conclusion. -/
theorem cuspidalPowerTraceIndependenceReduction :
    CuspidalPowerTraceIndependenceReductionStatement.{uF, uV} := fun hconv =>
  ⟨cuspidalPowerTraceIndependence_of_pairLogAsymptotics hconv,
    cuspidalPowerTraceIndependenceTC_of_pairLogAsymptotics hconv⟩

end Langlands.Automorphic.Unramified
