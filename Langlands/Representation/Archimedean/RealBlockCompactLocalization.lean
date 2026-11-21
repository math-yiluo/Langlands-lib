import Langlands.Representation.Archimedean.CompactSubgroupPowerLocalization
import Langlands.Representation.Archimedean.OrthogonalBlockPeak
import Langlands.Representation.Archimedean.RealInductionStagesInduce
import Langlands.Representation.Archimedean.RealLeviBlockHaar

/-! # Localization of real compact integrals on a block subgroup -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set

set_option autoImplicit false

namespace Langlands.Archimedean

open RealPrincipalSeriesDuality RealLeviBlockHaar InductionStages
open OrthogonalFinitePolynomial

attribute [local instance] measurableSpaceK secondCountableTopology_O

local instance borelSpaceK (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

variable {n c : ℕ}

/-- The compact block subgroup as a subgroup of the full compact group. -/
def blockCompactInclusion (cl : Fin n → Fin c) : Kc cl →* unitaryCompact ℝ n :=
  Subgroup.inclusion (fun _ h => h.1)

private theorem continuous_toUnitary (n : ℕ) : Continuous (toUnitary n) :=
  (Units.continuous_val.comp continuous_subtype_val).subtype_mk _

private instance (cl : Fin n → Fin c) : (μc cl).IsMulRightInvariant := by
  constructor
  intro g
  have hm : Measurable (fun x : Kc cl => x * g) :=
    (continuous_id.mul continuous_const).measurable
  have hmeasure : IsProbabilityMeasure (Measure.map (· * g) (μc cl)) :=
    ⟨by rw [Measure.map_apply hm MeasurableSet.univ, preimage_univ, measure_univ]⟩
  exact eq_μc cl _

/-- Positivity of full compact integrals tested against the squares of all
block-invariant real polynomials implies positivity of the block average. -/
def RealBlockCompactLocalizationStatement : Prop :=
  ∀ (n c : ℕ) (cl : Fin n → Fin c) (f : unitaryCompact ℝ n → ℝ), Continuous f →
    (∀ φ : Matrix.unitaryGroup (Fin n) ℝ → ℝ,
      Continuous φ → (fun k => (φ k : ℂ)) ∈ polynomialFunctions n →
      (∀ h : Kc cl, ∀ k, φ (toUnitary n (blockCompactInclusion cl h) * k) = φ k) →
      0 ≤ ∫ k, φ (toUnitary n k) ^ 2 * f k ∂haarK n) →
    0 ≤ ∫ h, f (blockCompactInclusion cl h) ∂μc cl

theorem realBlockCompactLocalization : RealBlockCompactLocalizationStatement := by
  intro n c cl f hf hInt
  let d : Fin n → ℝ := fun i => (cl i).val
  have hd (i j : Fin n) : d i = d j ↔ cl i = cl j := by
    simp only [d, Nat.cast_inj, Fin.ext_iff]
  obtain ⟨p, hp, hpPoly, hpRange, hpLevel, hpInv⟩ := orthogonalBlockPeak n d
  let ι := blockCompactInclusion cl
  have hι : Continuous ι := continuous_subtype_val.subtype_mk _
  have hmem (h : Kc cl) (i j : Fin n) (hij : d i ≠ d j) :
      (toUnitary n (ι h)).val i j = 0 :=
    h.2.2 i j (fun e => hij ((hd i j).2 e))
  have hpL (k : unitaryCompact ℝ n) :
      p (toUnitary n k) = 1 ↔ k ∈ range ι := by
    rw [hpLevel]
    constructor
    · intro hk
      refine ⟨⟨k.val, k.2, fun i j hij => hk i j (fun e => hij ((hd i j).1 e))⟩, ?_⟩
      exact Subtype.ext rfl
    · rintro ⟨h, rfl⟩
      exact hmem h
  have hpI (h : Kc cl) (k : unitaryCompact ℝ n) :
      p (toUnitary n (ι h * k)) = p (toUnitary n k) := by
    rw [map_mul]
    exact hpInv _ (hmem h) _
  let q : unitaryCompact ℝ n → ℝ := fun k => p (toUnitary n k) ^ 2
  have hqRange (k : unitaryCompact ℝ n) : q k ∈ Icc 0 1 := by
    obtain ⟨h₀, h₁⟩ := hpRange (toUnitary n k)
    exact ⟨pow_nonneg h₀ _, pow_le_one₀ h₀ h₁⟩
  have hqL (k : unitaryCompact ℝ n) : q k = 1 ↔ k ∈ range ι := by
    have hk := (hpRange (toUnitary n k)).1
    have he : q k = 1 ↔ p (toUnitary n k) = 1 := by
      constructor
      · intro h
        change p (toUnitary n k) ^ 2 = 1 at h
        nlinarith
      · intro h
        simp [q, h]
    exact he.trans (hpL k)
  refine compactSubgroupPowerLocalization ι (haarK n) (μc cl) hι
    ((hp.comp (continuous_toUnitary n)).pow 2) hf hqRange hqL ?_ ?_
  · intro h k
    change p (toUnitary n (ι h * k)) ^ 2 = p (toUnitary n k) ^ 2
    rw [hpI]
  · intro m
    let φ := fun k => p k ^ m
    have hPoly : (fun k => (φ k : ℂ)) ∈ polynomialFunctions n := by
      convert (polynomialFunctions n).pow_mem hpPoly m using 1
      funext k
      simp only [φ, Complex.ofReal_pow, Pi.pow_apply]
    have hv := hInt φ (hp.pow m) hPoly (fun h k => by
      change p (toUnitary n (ι h) * k) ^ m = p k ^ m
      rw [hpInv _ (hmem h)])
    change 0 ≤ ∫ k, (p (toUnitary n k) ^ 2) ^ m * f k ∂haarK n
    simpa only [φ, ← pow_mul, Nat.mul_comm m 2] using hv

end Langlands.Archimedean
