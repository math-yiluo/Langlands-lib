import Langlands.Automorphic.RegularAlgebraic
import Langlands.LocalFactor.ArchimedeanAttachment
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Perm.Basic

/-!
# Complex-place exponent coordinates and highest weights

Internal vocabulary translating the signed polar character convention into
Clozel's exponent coordinates. The two Weyl permutations are independent.
No existence or comparison theorem for automorphic parameters is asserted.
-/

noncomputable section

universe uF

set_option autoImplicit false

namespace Langlands.LocalFactor.Archimedean.ComplexCharacterData

/-- The `z` exponent of the single-valued polar character, using its signed weight. -/
def zExponent (d : ComplexCharacterData) : ℂ :=
  d.exponent + (d.weight : ℂ) / 2

/-- The conjugate-`z` exponent of the same polar character. -/
def zBarExponent (d : ComplexCharacterData) : ℂ :=
  d.exponent - (d.weight : ℂ) / 2

end Langlands.LocalFactor.Archimedean.ComplexCharacterData

namespace Langlands.Automorphic.ComplexPlaceParameter

open Langlands.LocalFactor.Archimedean
open Langlands.Global
open NumberField NumberField.InfinitePlace

/-- The half-sum of positive roots for the upper triangular Borel, indexed from zero.
All subtractions, including `n - 1`, take place in `ℂ`. -/
def rho (n : ℕ) (i : Fin n) : ℂ :=
  ((n : ℂ) - 1) / 2 - (i.val : ℂ)

/-- Each exponent list is the corresponding shifted highest weight up to its own
Weyl permutation. No pairing between the two permutations is required. -/
def MatchesHighestWeight (n : ℕ) (ds : List ComplexCharacterData)
    (μz μzBar : Fin n → ℂ) : Prop :=
  ds.length = n ∧
    (ds.map ComplexCharacterData.zExponent).Perm
      (List.ofFn fun i => μz i + rho n i) ∧
    (ds.map ComplexCharacterData.zBarExponent).Perm
      (List.ofFn fun i => μzBar i + rho n i)

/-- Both exponent lists are regular and lie in `(n - 1) / 2 + ℤ`.
There is no purity, unitarity or paired-order condition. -/
def IsClozelRegularAlgebraic (n : ℕ) (ds : List ComplexCharacterData) : Prop :=
  ds.length = n ∧
    (∀ d ∈ ds, ∃ p q : ℤ,
      d.zExponent = (p : ℂ) + ((n : ℂ) - 1) / 2 ∧
      d.zBarExponent = (q : ℂ) + ((n : ℂ) - 1) / 2) ∧
    (ds.map ComplexCharacterData.zExponent).Nodup ∧
    (ds.map ComplexCharacterData.zBarExponent).Nodup

/-- Complex-place matching with the published embedding orientation:
`false` reads `z`, and `true` reads its complex conjugate. Real indices are unrestricted. -/
def MatchesGlobalHighestWeight (F : Type uF) [Field F] [NumberField F] (n : ℕ)
    (ds : {v : NumberField.InfinitePlace F // IsComplex v} → List ComplexCharacterData)
    (μ : ArchimedeanGL.EmbeddingIndex F → Fin n → ℂ) : Prop :=
  ∀ v, MatchesHighestWeight n (ds v) (μ (.inr (v, false))) (μ (.inr (v, true)))

/-- A relation to an actual character of the global enveloping center, witnessed
by a highest weight with matching complex coordinates. It asserts no existence or uniqueness. -/
def MatchesInfinitesimalCharacter (F : Type uF) [Field F] [NumberField F] (n : ℕ)
    (ds : {v : NumberField.InfinitePlace F // IsComplex v} → List ComplexCharacterData)
    (χ : ArchimedeanGL.EnvelopingCenter F n →ₐ[ℂ] ℂ) : Prop :=
  ∃ μ : ArchimedeanGL.EmbeddingIndex F → Fin n → ℂ,
    ArchimedeanGL.IsHighestWeightCharacter F n μ χ ∧
      MatchesGlobalHighestWeight F n ds μ

/-- Reordering the blocks preserves the two independent shifted Weyl orbits. -/
theorem matchesHighestWeight_iff_of_perm {n : ℕ}
    {ds ds' : List ComplexCharacterData} (h : ds.Perm ds') (μz μzBar : Fin n → ℂ) :
    MatchesHighestWeight n ds μz μzBar ↔ MatchesHighestWeight n ds' μz μzBar := by
  constructor
  · rintro ⟨hlen, hz, hzBar⟩
    exact ⟨h.length_eq.symm.trans hlen,
      (h.map ComplexCharacterData.zExponent).symm.trans hz,
      (h.map ComplexCharacterData.zBarExponent).symm.trans hzBar⟩
  · rintro ⟨hlen, hz, hzBar⟩
    exact ⟨h.length_eq.trans hlen,
      (h.map ComplexCharacterData.zExponent).trans hz,
      (h.map ComplexCharacterData.zBarExponent).trans hzBar⟩

/-- Integrality cosets and separate regularity do not depend on the block order. -/
theorem isClozelRegularAlgebraic_iff_of_perm {n : ℕ}
    {ds ds' : List ComplexCharacterData} (h : ds.Perm ds') :
    IsClozelRegularAlgebraic n ds ↔ IsClozelRegularAlgebraic n ds' := by
  constructor
  · rintro ⟨hlen, hint, hz, hzBar⟩
    exact ⟨h.length_eq.symm.trans hlen, fun d hd => hint d (h.mem_iff.mpr hd),
      (h.map ComplexCharacterData.zExponent).nodup_iff.mp hz,
      (h.map ComplexCharacterData.zBarExponent).nodup_iff.mp hzBar⟩
  · rintro ⟨hlen, hint, hz, hzBar⟩
    exact ⟨h.length_eq.trans hlen, fun d hd => hint d (h.mem_iff.mp hd),
      (h.map ComplexCharacterData.zExponent).nodup_iff.mpr hz,
      (h.map ComplexCharacterData.zBarExponent).nodup_iff.mpr hzBar⟩

/-- Pointwise block permutations preserve matching with the same global highest weight. -/
theorem matchesGlobalHighestWeight_iff_of_perm
    {F : Type uF} [Field F] [NumberField F] {n : ℕ}
    {ds ds' : {v : NumberField.InfinitePlace F // IsComplex v} → List ComplexCharacterData}
    (h : ∀ v, (ds v).Perm (ds' v))
    (μ : ArchimedeanGL.EmbeddingIndex F → Fin n → ℂ) :
    MatchesGlobalHighestWeight F n ds μ ↔ MatchesGlobalHighestWeight F n ds' μ := by
  constructor
  · intro hw v
    exact (matchesHighestWeight_iff_of_perm (h v) _ _).mp (hw v)
  · intro hw v
    exact (matchesHighestWeight_iff_of_perm (h v) _ _).mpr (hw v)

/-- Pointwise block permutations preserve matching with the same actual center character. -/
theorem matchesInfinitesimalCharacter_iff_of_perm
    {F : Type uF} [Field F] [NumberField F] {n : ℕ}
    {ds ds' : {v : NumberField.InfinitePlace F // IsComplex v} → List ComplexCharacterData}
    (h : ∀ v, (ds v).Perm (ds' v))
    (χ : ArchimedeanGL.EnvelopingCenter F n →ₐ[ℂ] ℂ) :
    MatchesInfinitesimalCharacter F n ds χ ↔ MatchesInfinitesimalCharacter F n ds' χ := by
  constructor
  · rintro ⟨μ, hχ, hw⟩
    exact ⟨μ, hχ, (matchesGlobalHighestWeight_iff_of_perm h μ).mp hw⟩
  · rintro ⟨μ, hχ, hw⟩
    exact ⟨μ, hχ, (matchesGlobalHighestWeight_iff_of_perm h μ).mpr hw⟩

end Langlands.Automorphic.ComplexPlaceParameter
