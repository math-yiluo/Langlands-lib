import Langlands.Global.AdelicConeShiftEquationDecay
import Langlands.Global.AdelicEisensteinConstantTermWeakApproximationStatement

/-! # The constant term on cones from the remainder of the weak constant term

`eisensteinConstantTermWeakApproximation_of_remainder` derives
`EisensteinConstantTermWeakApproximationStatement` (Delorme 2023, the bound for `E_Q − E^w_Q` in
the proofs of Lemmas 5.1–5.3) from `EisensteinWeakConstantTermRemainderStatement`: the remainder
`E_Q − ∑ c_q Φ_q` has a unitary central character, the polynomial bound (5.1) on Siegel sets and
cone shift equations, and `ConeShiftDecay.exists_coneBound` turns these into the cone estimate. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  AdelicSiegelFactors Langlands.Analysis.Meromorphic PositiveRealTorus

/-- **The constant term of Eisenstein series on cones from the remainder of its weak constant
term.** The remainder statement, applied with the threshold `min(t, 1)`, gives the triples and
the three properties of the remainder; `ConeShiftDecay.exists_coneBound` gives the cone estimate
with rate `ε δ / 4`. -/
theorem eisensteinConstantTermWeakApproximation_of_remainder
    (h : EisensteinWeakConstantTermRemainderStatement) :
    EisensteinConstantTermWeakApproximationStatement := by
  intro F _ _ G P M U A _ _ _ _ _ _ p _ iU l a r _ _ _ hA hT hG hU K hK N d rho hsmooth
    hcalc φ hKmax hrho hφ E D hD hmero hreg n e C hC T i ν T₀ j hset hK0 J hJ hJne hKQ δ hδ t Ω
    hΩ
  have htpos : (0 : ℝ≥0) < (t : ℝ≥0) := (Units.ne_zero t).bot_lt
  let t' : ℝ≥0ˣ := Units.mk0 (min (t : ℝ≥0) 1) (lt_min htpos one_pos).ne'
  have ht't : t' ≤ t := Units.val_le_val.mp (by
    change min (t : ℝ≥0) 1 ≤ (t : ℝ≥0)
    exact min_le_left _ _)
  have ht'1 : t' ≤ 1 := Units.val_le_val.mp (by
    change min (t : ℝ≥0) 1 ≤ ((1 : ℝ≥0ˣ) : ℝ≥0)
    rw [Units.val_one]
    exact min_le_right _ _)
  obtain ⟨ε, m, B, k, c, V, L, Φ, hε, hc, hL, hshift, hcont, hΦ, hcent, hpoly, hcone⟩ :=
    h F G P M U A p iU l a r hA hT hG hU K hK rho hsmooth hcalc φ hKmax hrho hφ E D hD hmero
      hreg n e C hC T i ν T₀ j hset hK0 J hJ hJne hKQ δ hδ t' Ω hΩ
  obtain ⟨α₀, hα₀, hα₀J⟩ := hJne
  obtain ⟨B', hB'⟩ := ConeShiftDecay.exists_coneBound hG hset rho hJ hα₀ hα₀J hδ hε m B
    ht't ht'1 hΩ
  have hmono : ∀ b ∈ PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t,
      b ∈ PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t' :=
    fun b hb χ hχ => le_trans ht't (hb χ hχ)
  refine ⟨ε * δ / 4, m, max B B', k, c, V, L, Φ, by positivity, hc, hL, hshift, hcont, ?_, ?_⟩
  · intro q x hx z hz b hb ω hω
    refine (hΦ q x hx z hz b (hmono b hb) ω hω).trans ?_
    have hσ : 0 ≤ adelicLogHeight F G rho (z * positiveMap F G T i T₀ j b * ω) := by
      unfold adelicLogHeight
      have := Real.log_nonneg (le_max_left 1
        (RepresentationGrowth.adelicSourceNorm F G rho (z * positiveMap F G T i T₀ j b * ω)))
      linarith
    have hs : 0 ≤ Real.sqrt (siegelModulus F G T i ν T₀ j b) := Real.sqrt_nonneg _
    gcongr
    exact le_max_left _ _
  · intro x hx z hz b hb ω hω R hR hα
    refine (hB' _ (hcent x hx) (hpoly x hx) (hcone x hx) z hz b hb ω hω R hR hα).trans ?_
    have hs : 0 ≤ Real.sqrt (siegelModulus F G T i ν T₀ j b) := Real.sqrt_nonneg _
    gcongr
    exact le_max_right _ _

end Langlands.Global
