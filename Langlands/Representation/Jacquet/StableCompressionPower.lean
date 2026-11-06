import Langlands.Representation.Jacquet.CompressionStabilizationStatement
import Langlands.LinearAlgebra.StableEndomorphismProofs

/-! # Fixed-exponent stability of compact compression

The algebraic passage from a positive stable power to stationary power chains
and their complementary limits. No existence of a stable power is assumed
implicitly or proved for arbitrary smooth representations.
-/

namespace Langlands.Jacquet

universe uG uV

open Langlands.LinearAlgebra.StableEndomorphism

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The `b`-th power of the actual compressed action satisfies Renard's two
stability equalities. The positivity of `b` is supplied separately. -/
def CompactCompressionStablePower (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G) (b : ℕ) : Prop :=
  Stable (compressedAction ρ hρ K hK g ^ b)

/-- The exact stationary-chain and complementarity conclusions, with an
explicit common threshold. -/
def CompactCompressionStationaryFrom (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G) (b : ℕ) : Prop :=
  (∀ s : ℕ, b ≤ s →
    stableImage ρ hρ K hK g = LinearMap.range (compressedAction ρ hρ K hK g ^ s) ∧
      powerKernelSup ρ hρ K hK g = LinearMap.ker (compressedAction ρ hρ K hK g ^ s)) ∧
    CompactCompressionSplits ρ hρ K hK g

/-- Renard's stable-power criterion for a fixed exponent. -/
theorem compactCompressionStablePower_iff_isCompl
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G) (b : ℕ) :
    CompactCompressionStablePower ρ hρ K hK g b ↔
      IsCompl (LinearMap.ker (compressedAction ρ hρ K hK g ^ b))
        (LinearMap.range (compressedAction ρ hρ K hK g ^ b)) :=
  stable_iff_isCompl _

/-- A positive stable power gives the exact stationary power-chain conclusions
from the same exponent, without any dimension hypothesis. -/
theorem compactCompressionStationaryFrom_of_stablePower
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    {b : ℕ} (hb : 0 < b) (h : CompactCompressionStablePower ρ hρ K hK g b) :
    CompactCompressionStationaryFrom ρ hρ K hK g b := by
  let C := compressedAction ρ hρ K hK g
  change Stable (C ^ b) at h
  have hstable := h
  obtain ⟨hker, hrange⟩ := h
  rw [← pow_mul] at hker hrange
  have hle : b + 1 ≤ b * 2 := by omega
  have hk : LinearMap.ker (C ^ b) = LinearMap.ker (C ^ (b + 1)) :=
    le_antisymm (ker_pow_monotone C (Nat.le_succ b))
      (hker ▸ ker_pow_monotone C hle)
  have hr : LinearMap.range (C ^ b) = LinearMap.range (C ^ (b + 1)) :=
    le_antisymm (hrange ▸ range_pow_antitone C hle)
      (range_pow_antitone C (Nat.le_succ b))
  have hkall : powerKernelSup ρ hρ K hK g = LinearMap.ker (C ^ b) := by
    apply le_antisymm
    · apply iSup_le
      intro r
      by_cases hbr : b ≤ r
      · exact (ker_pow_eq_of_le hk hbr).le
      · exact ker_pow_monotone C (by omega)
    · exact le_iSup (fun r : ℕ => LinearMap.ker (C ^ r)) b
  have hrall : stableImage ρ hρ K hK g = LinearMap.range (C ^ b) := by
    apply le_antisymm
    · exact iInf_le (fun r : ℕ => LinearMap.range (C ^ r)) b
    · apply le_iInf
      intro r
      by_cases hbr : b ≤ r
      · exact (range_pow_eq_of_le hr hbr).symm.le
      · exact range_pow_antitone C (by omega)
  constructor
  · intro s hs
    exact ⟨hrall.trans (range_pow_eq_of_le hr hs).symm,
      hkall.trans (ker_pow_eq_of_le hk hs).symm⟩
  · change IsCompl (powerKernelSup ρ hρ K hK g) (stableImage ρ hρ K hK g)
    rw [hkall, hrall]
    exact (stable_iff_isCompl (C ^ b)).mp hstable

/-- The target's stationary-chain conclusion implies stability of the power
at its threshold, even when that threshold is zero. -/
theorem compactCompressionStablePower_of_stationaryFrom
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    {b : ℕ} (h : CompactCompressionStationaryFrom ρ hρ K hK g b) :
    CompactCompressionStablePower ρ hρ K hK g b := by
  obtain ⟨hbR, hbK⟩ := h.1 b le_rfl
  obtain ⟨h2R, h2K⟩ := h.1 (b * 2) (by omega)
  change Stable (compressedAction ρ hρ K hK g ^ b)
  constructor <;> rw [← pow_mul]
  · exact hbK.symm.trans h2K
  · exact hbR.symm.trans h2R

/-- For a positive exponent, stable power and stationary chains with splitting
are equivalent formulations. -/
theorem compactCompressionStationaryFrom_iff_stablePower
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    {b : ℕ} (hb : 0 < b) :
    CompactCompressionStationaryFrom ρ hρ K hK g b ↔
      CompactCompressionStablePower ρ hρ K hK g b :=
  ⟨compactCompressionStablePower_of_stationaryFrom ρ hρ K hK g,
    compactCompressionStationaryFrom_of_stablePower ρ hρ K hK g hb⟩

/-- Increasing the common threshold preserves every conclusion. -/
theorem CompactCompressionStationaryFrom.mono
    {ρ : Representation ℂ G V} {hρ : IsSmooth ρ}
    {K : OpenSubgroup G} {hK : IsCompact (K : Set G)} {g : G}
    {b c : ℕ} (h : CompactCompressionStationaryFrom ρ hρ K hK g b) (hbc : b ≤ c) :
    CompactCompressionStationaryFrom ρ hρ K hK g c :=
  ⟨fun s hs => h.1 s (hbc.trans hs), h.2⟩

/-- Existential stationary chains and splitting are equivalent to existence of
one positive stable power. The zero-threshold case is replaced by threshold one. -/
theorem compactCompression_eventuallyStable_iff_exists_stationaryFrom
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G) :
    EventuallyStable (compressedAction ρ hρ K hK g) ↔
      ∃ b : ℕ, CompactCompressionStationaryFrom ρ hρ K hK g b := by
  constructor
  · rintro ⟨b, hb, h⟩
    exact ⟨b, compactCompressionStationaryFrom_of_stablePower ρ hρ K hK g hb h⟩
  · rintro ⟨b, h⟩
    refine ⟨max b 1, by omega, ?_⟩
    exact compactCompressionStablePower_of_stationaryFrom ρ hρ K hK g
      (h.mono (Nat.le_max_left _ _))

end Langlands.Jacquet
