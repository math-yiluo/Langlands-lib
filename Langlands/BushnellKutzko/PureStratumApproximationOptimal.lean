import Langlands.BushnellKutzko.PureStratumApproximationCandidateBound

/-! # An optimal candidate approximation

The choice made in the proof of BK93 (2.4.1)(i), printed p. 67 (just before (2.4.5)):
maximal degree first, then minimal normalized depth, without compactness.
-/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.PureApproximation

universe uF uV

/-- If some simple stratum whose coset contains the element of a pure stratum `S` generates an
algebra of smaller degree, then there is such a candidate of maximal degree that also has minimal
normalized depth `r / e` among the candidates of that degree. -/
def OptimalCandidateStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (V : Type uV) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (S : Stratum 𝒪[F] F V), S.IsPure →
    (∃ T : Stratum 𝒪[F] F V,
      T.IsSimple ∧ S.b ∈ T.coset ∧ elementDegree F T.b < elementDegree F S.b) →
    ∃ T₀ : Stratum 𝒪[F] F V,
      (T₀.IsSimple ∧ S.b ∈ T₀.coset ∧ elementDegree F T₀.b < elementDegree F S.b) ∧
      ∀ T : Stratum 𝒪[F] F V, T.IsSimple → S.b ∈ T.coset →
        elementDegree F T.b < elementDegree F S.b →
        elementDegree F T.b ≤ elementDegree F T₀.b ∧
        (elementDegree F T.b = elementDegree F T₀.b →
          T₀.r * T.chain.period ≤ T.r * T₀.chain.period)

/-- Maximize the degree with `Nat.findGreatest`, then minimize `r · ((dim V)! / e)`. -/
theorem optimalCandidate : OptimalCandidateStatement.{uF, uV} := by
  intro F _ _ _ _ V _ _ _ S hS hex
  classical
  let Cand : Stratum 𝒪[F] F V → Prop := fun T =>
    T.IsSimple ∧ S.b ∈ T.coset ∧ elementDegree F T.b < elementDegree F S.b
  obtain ⟨T₁, hT₁⟩ := hex
  -- The maximal degree of a candidate.
  let P : ℕ → Prop := fun k => ∃ T, Cand T ∧ elementDegree F T.b = k
  let d := Nat.findGreatest P (elementDegree F S.b)
  have hPd : P d := Nat.findGreatest_spec (le_of_lt hT₁.2.2) ⟨T₁, hT₁, rfl⟩
  have hmax (T : Stratum 𝒪[F] F V) (hT : Cand T) : elementDegree F T.b ≤ d :=
    Nat.le_findGreatest (le_of_lt hT.2.2) ⟨T, hT, rfl⟩
  -- Normalized depths, scaled by `K = (dim V)!` to integers.
  obtain ⟨m, hm⟩ := candidateDepthBound_aux S hS
  set K : ℕ := (Module.finrank F V).factorial with hK
  have hK0 : (0 : ℤ) < K := by exact_mod_cast Nat.factorial_pos _
  have hdvd (T : Stratum 𝒪[F] F V) : T.chain.period ∣ K :=
    Nat.dvd_factorial T.chain.period_pos (period_le_finrank T.chain)
  have hmul (T : Stratum 𝒪[F] F V) :
      (T.chain.period : ℤ) * ((K / T.chain.period : ℕ) : ℤ) = K := by
    exact_mod_cast Nat.mul_div_cancel' (hdvd T)
  let q : Stratum 𝒪[F] F V → ℤ := fun T => T.r * ((K / T.chain.period : ℕ) : ℤ)
  let Q : ℤ → Prop := fun z => ∃ T, Cand T ∧ elementDegree F T.b = d ∧ q T = z
  have hQb : ∃ b : ℤ, ∀ z : ℤ, Q z → b ≤ z := by
    refine ⟨m * K, fun z hzQ => ?_⟩
    obtain ⟨T, hT, _, hz⟩ := hzQ
    rw [← hz]
    have h1 := hm T hT.1.1 hT.2.1 hT.2.2
    have hk : (0 : ℤ) ≤ ((K / T.chain.period : ℕ) : ℤ) := by positivity
    have h2 := mul_le_mul_of_nonneg_right h1 hk
    calc m * (K : ℤ) = m * T.chain.period * ((K / T.chain.period : ℕ) : ℤ) := by
          rw [mul_assoc, hmul T]
      _ ≤ T.r * ((K / T.chain.period : ℕ) : ℤ) := h2
  obtain ⟨T₂, hT₂, hT₂d⟩ := hPd
  obtain ⟨z₀, ⟨T₀, hT₀, hT₀d, hq₀⟩, hz₀⟩ :=
    Int.exists_least_of_bdd hQb ⟨q T₂, T₂, hT₂, hT₂d, rfl⟩
  refine ⟨T₀, hT₀, fun T hTs hTβ hTdeg => ?_⟩
  have hT : Cand T := ⟨hTs, hTβ, hTdeg⟩
  refine ⟨hT₀d ▸ hmax T hT, fun hdeq => ?_⟩
  have hle : q T₀ ≤ q T := by
    rw [hq₀]
    exact hz₀ _ ⟨T, hT, hdeq.trans hT₀d, rfl⟩
  -- Clear the denominators.
  set e₀ : ℤ := (T₀.chain.period : ℤ) with he₀
  set e : ℤ := (T.chain.period : ℤ) with he
  set k₀ : ℤ := ((K / T₀.chain.period : ℕ) : ℤ) with hk₀
  set k : ℤ := ((K / T.chain.period : ℕ) : ℤ) with hk
  have he₀0 : 0 < e₀ := by rw [he₀]; exact_mod_cast T₀.chain.period_pos
  have he0 : 0 < e := by rw [he]; exact_mod_cast T.chain.period_pos
  have hm₀ : e₀ * k₀ = K := hmul T₀
  have hmT : e * k = K := hmul T
  have hle' : T₀.r * k₀ ≤ T.r * k := hle
  have hpos : 0 < e₀ * e := mul_pos he₀0 he0
  have h3 := mul_le_mul_of_nonneg_right hle' hpos.le
  have h4 : (T₀.r * e) * K ≤ (T.r * e₀) * K := by
    calc (T₀.r * e) * K = (T₀.r * k₀) * (e₀ * e) := by rw [← hm₀]; ring
      _ ≤ (T.r * k) * (e₀ * e) := h3
      _ = (T.r * e₀) * K := by rw [← hmT]; ring
  exact le_of_mul_le_mul_right h4 hK0

end Langlands.BushnellKutzko.PureApproximation
