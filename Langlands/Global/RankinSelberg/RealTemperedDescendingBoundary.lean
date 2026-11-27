import Langlands.Global.RankinSelberg.RealDescendingWhittakerRange
import Langlands.Global.RankinSelberg.RealMatrixPairIdentity
import Langlands.Global.RankinSelberg.RealTemperedCharacterBound
import Langlands.Global.RankinSelberg.RealTemperedWhittakerBound

/-! # A boundary estimate for the tempered bound of real block coefficients -/

noncomputable section

open Langlands.Archimedean Langlands.LocalFactor.Archimedean

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealTemperedWhittaker

open ArchimedeanLocal RealIwasawa RealGodement RealGodementProfiles RealPrincipalSeries

local notation "V[" n ", " ds "]" => Automorphic.realStandardKFinite n ds

/-- A nearby-line estimate on the canonical family with the compact profile of a block
vector. The spectral family passes through the descending position exponents. -/
def RealDescendingCanonicalLineBoundAtRank (r : ℕ) : Prop :=
  ∀ (ds : List RealBlock), realRank ds = r + 1 → (∀ d ∈ ds, realBlockExponent d = 0) →
    ∀ (a : ℝˣ) (p : Fin (r + 1) → Fin 2) (z : Fin (r + 1) → ℂ), expand ds = characterList p z →
      ∀ (h : V[r + 1, ds] ≤ V[r + 1, characterList p z]) (f : V[r + 1, ds]),
        let profile := isCompactProfile_compactRestriction (Submodule.inclusion h f).property
        ∃ (q : ℂ → Fin (r + 1) → ℂ), Differentiable ℂ q ∧ q 0 = z ∧ ∃ D : ℝ, 0 ≤ D ∧
          ∀ δ ∈ Set.Ioo (0 : ℝ) 1, ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℂ, t.re = δ → |t.im| ≤ 1 →
            ∀ (y : Fin (r + 1) → ℝ) (k : unitaryCompact ℝ (r + 1)),
              ‖canonicalJacquetFamily a profile (q t) (torus y * k.val)‖ ≤
                A * Real.exp (torusModularLog (r + 1) y / 2 + D * δ * ∑ i, |y i|)

/-- The boundary estimate on descending families suffices for the exact-model
tempered bound at the same rank. -/
def RealTemperedDescendingBoundaryStatement : Prop :=
  ∀ r : ℕ, RealDescendingCanonicalLineBoundAtRank r → RealTemperedWhittakerBoundAtRank r

theorem realTemperedWhittakerBoundAtRank_of_descendingCanonicalLines :
    RealTemperedDescendingBoundaryStatement := by
  intro r hBoundary ds hr him a W hW ε hε
  obtain ⟨cs, hcs⟩ := Langlands.GodementJacquet.exists_expand_eq_map_character ds
  have hr' : realRank (cs.map RealBlock.character) = r + 1 :=
    hcs ▸ (realRank_expand ds).trans hr
  obtain ⟨p, z, hpz⟩ := exists_characterList_of_map_character cs hr'
  have he := hcs.trans hpz
  have hIncl : V[r + 1, ds] ≤ V[r + 1, characterList p z] :=
    he ▸ realStandardKFinite_le_expand (r + 1) ds
  rw [← neg_neg a, realWhittakerModel_eq_range_descendingCanonical r ds hr (-a) p z he hIncl] at hW
  obtain ⟨f, rfl⟩ := hW
  let profile := isCompactProfile_compactRestriction (Submodule.inclusion hIncl f).property
  obtain ⟨q, hq, hzero, D, hD, hb⟩ := hBoundary ds hr him (-a) p z he hIncl f
  have h := canonicalTemperedBound_of_rightBoundary (-a) profile q hq hD hb ε hε
  rw [hzero] at h
  exact h

end Langlands.Global.RankinSelbergGlobal.RealTemperedWhittaker
