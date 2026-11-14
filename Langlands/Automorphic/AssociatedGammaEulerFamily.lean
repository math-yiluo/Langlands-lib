import Langlands.Global.Factors.HeckeTwistComparisonStatement

/-!
# Hecke Euler families with chosen partial L-functions

The two-twist comparison engine needs, for each character and finite exceptional set,
partial L-functions satisfying admissibility, Euler products and the functional equation.
Only their existence matters, so a family is built from its local factors by choosing
partial L-functions whenever such exist. The common-twist analytic input then reduces to
existence statements and to equality of local L-factors outside the exceptional set.
-/

noncomputable section

set_option autoImplicit false

open scoped BigOperators

universe u

namespace Langlands.Global.FunctionalEquationComparison

namespace HeckeEulerFamily

variable {K : Type u} [Field K] [NumberField K]

/-- Local factors `l` at all places admit partial L-functions outside the exceptional set
`univ.disjSum B` satisfying admissibility, Euler products on a right half-plane and the
functional equation. -/
def HasEngineInputs (l : AllPlaces K → LocalFactors) (B : Finset (FinitePlace K)) : Prop := by
  classical
  exact ∃ (σ : ℝ) (Lp Lpd : ℂ → ℂ),
    Admissible (FiniteEulerData.mk l Lp Lpd) (exceptionalPlaces K B) ∧
    HasEulerProductsOutside (FiniteEulerData.mk l Lp Lpd) (exceptionalPlaces K B) σ ∧
    FunctionalEquation (FiniteEulerData.mk l Lp Lpd) (exceptionalPlaces K B)

open Classical in
/-- Partial L-functions witnessing `HasEngineInputs`, or `0` if there are none. -/
def choosePartial (l : HeckeCharacter K → AllPlaces K → LocalFactors) (χ : HeckeCharacter K)
    (B : Finset (FinitePlace K)) : (ℂ → ℂ) × (ℂ → ℂ) :=
  if h : HasEngineInputs (l χ) B then (h.choose_spec.choose, h.choose_spec.choose_spec.choose)
  else (0, 0)

/-- The Hecke Euler family with local factors `l` and chosen partial L-functions. -/
def ofLocalFactors (l : HeckeCharacter K → AllPlaces K → LocalFactors) : HeckeEulerFamily K where
  localFactors := l
  partialL χ B := (choosePartial l χ B).1
  partialDualL χ B := (choosePartial l χ B).2

/-- If the engine inputs exist, the chosen partial L-functions satisfy them. -/
theorem ofLocalFactors_spec [DecidableEq (AllPlaces K)]
    (l : HeckeCharacter K → AllPlaces K → LocalFactors) (χ : HeckeCharacter K)
    (B : Finset (FinitePlace K)) (h : HasEngineInputs (l χ) B) :
    ∃ σ : ℝ, Admissible ((ofLocalFactors l).eulerData χ B) (exceptionalPlaces K B) ∧
      HasEulerProductsOutside ((ofLocalFactors l).eulerData χ B) (exceptionalPlaces K B) σ ∧
      FunctionalEquation ((ofLocalFactors l).eulerData χ B) (exceptionalPlaces K B) := by
  have hspec := h.choose_spec.choose_spec.choose_spec
  have hD : (ofLocalFactors l).eulerData χ B =
      FiniteEulerData.mk (l χ) h.choose_spec.choose h.choose_spec.choose_spec.choose := by
    simp only [eulerData, ofLocalFactors, choosePartial, h, ↓reduceDIte]
  rw [hD]
  exact ⟨h.choose, hspec.1, hspec.2.1, hspec.2.2⟩

/-- Euler products on a half-plane persist on smaller half-planes. -/
theorem hasEulerProductsOutside_mono {Place : Type*} [DecidableEq Place]
    {D : FiniteEulerData Place} {S : Finset Place} {σ σ' : ℝ} (hσ : σ ≤ σ')
    (h : HasEulerProductsOutside D S σ) : HasEulerProductsOutside D S σ' :=
  fun s hs => h s (lt_of_le_of_lt hσ hs)

/-- Local L-factors at finite places outside `B` that agree on a half-plane give
`MatchesOutside` at `univ.disjSum B`. -/
theorem matchesOutside_exceptionalPlaces [DecidableEq (AllPlaces K)]
    {D E : FiniteEulerData (AllPlaces K)} {B : Finset (FinitePlace K)} {σ : ℝ}
    (h : ∀ v ∉ B, ∀ s : ℂ, σ < s.re →
      (D.localFactors (.inr v)).lFactor s = (E.localFactors (.inr v)).lFactor s ∧
        (D.localFactors (.inr v)).dualLFactor s = (E.localFactors (.inr v)).dualLFactor s) :
    MatchesOutside D E (exceptionalPlaces K B) σ := by
  intro z hz s hs
  cases z with
  | inl w =>
    exact absurd (by simp [exceptionalPlaces]) hz
  | inr v =>
    exact h v (fun hv => hz (by simpa [exceptionalPlaces] using hv)) s hs

/-- The common-twist analytic input for families built from local factors: for any two
finite-order characters trivial at infinity, a finite set `B ⊇ T` outside which both are
unramified, the engine inputs for both families and both characters at `B`, and agreement of
the finite local L-factors outside `B` on a right half-plane. -/
theorem commonTwistEulerInputs_ofLocalFactors (T : Finset (FinitePlace K))
    (lD lE : HeckeCharacter K → AllPlaces K → LocalFactors)
    (h : ∀ χ₁ χ₂ : HeckeCharacter K, χ₁.HasFiniteOrder → χ₂.HasFiniteOrder →
      χ₁.HasPrescribedInfinityComponent 1 → χ₂.HasPrescribedInfinityComponent 1 →
      ∃ B : Finset (FinitePlace K), T ⊆ B ∧
        (∀ v ∉ B, χ₁.IsUnramifiedAt v ∧ χ₂.IsUnramifiedAt v) ∧
        HasEngineInputs (lD χ₁) B ∧ HasEngineInputs (lE χ₁) B ∧
        HasEngineInputs (lD χ₂) B ∧ HasEngineInputs (lE χ₂) B ∧
        ∃ σ : ℝ, ∀ v ∉ B, ∀ s : ℂ, σ < s.re →
          ((lD χ₁ (.inr v)).lFactor s = (lE χ₁ (.inr v)).lFactor s ∧
            (lD χ₁ (.inr v)).dualLFactor s = (lE χ₁ (.inr v)).dualLFactor s) ∧
          ((lD χ₂ (.inr v)).lFactor s = (lE χ₂ (.inr v)).lFactor s ∧
            (lD χ₂ (.inr v)).dualLFactor s = (lE χ₂ (.inr v)).dualLFactor s)) :
    CommonTwistEulerInputs K T (ofLocalFactors lD) (ofLocalFactors lE) := by
  classical
  intro χ₁ χ₂ h₁ h₂ h₁' h₂'
  obtain ⟨B, hTB, hunr, hD₁, hE₁, hD₂, hE₂, σ, hmatch⟩ := h χ₁ χ₂ h₁ h₂ h₁' h₂'
  obtain ⟨σD₁, aD₁, pD₁, fD₁⟩ := ofLocalFactors_spec lD χ₁ B hD₁
  obtain ⟨σE₁, aE₁, pE₁, fE₁⟩ := ofLocalFactors_spec lE χ₁ B hE₁
  obtain ⟨σD₂, aD₂, pD₂, fD₂⟩ := ofLocalFactors_spec lD χ₂ B hD₂
  obtain ⟨σE₂, aE₂, pE₂, fE₂⟩ := ofLocalFactors_spec lE χ₂ B hE₂
  refine ⟨B, hTB, hunr, aD₁, aE₁, aD₂, aE₂, fD₁, fE₁, fD₂, fE₂,
    max σ (max σD₁ σE₁), max σ (max σD₂ σE₂), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hasEulerProductsOutside_mono
      ((le_max_left _ _).trans (le_max_right _ _)) pD₁
  · exact hasEulerProductsOutside_mono
      ((le_max_right _ _).trans (le_max_right _ _)) pE₁
  · exact matchesOutside_exceptionalPlaces fun v hv s hs =>
      (hmatch v hv s (lt_of_le_of_lt (le_max_left _ _) hs)).1
  · exact hasEulerProductsOutside_mono
      ((le_max_left _ _).trans (le_max_right _ _)) pD₂
  · exact hasEulerProductsOutside_mono
      ((le_max_right _ _).trans (le_max_right _ _)) pE₂
  · exact matchesOutside_exceptionalPlaces fun v hv s hs =>
      (hmatch v hv s (lt_of_le_of_lt (le_max_left _ _) hs)).2

end HeckeEulerFamily

end Langlands.Global.FunctionalEquationComparison
