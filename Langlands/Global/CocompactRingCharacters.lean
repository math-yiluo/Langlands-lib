import Langlands.Global.RingPontryaginPairing
import Langlands.HarmonicAnalysis.CompactQuotientCharacters
import Mathlib.Algebra.Group.Subgroup.Map

/-! # Character parametrization from a cocompact field in a ring -/

noncomputable section

universe u v

namespace Langlands.Global.CocompactRingCharacters

variable {K : Type u} [Field K]
variable {R : Type v} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- The additive image of a field, with multiplicative notation for its group. -/
def fieldImage (ι : K →+* R) : Subgroup (Multiplicative R) :=
  ι.toAddMonoidHom.toMultiplicative.range

omit [TopologicalSpace R] [IsTopologicalRing R] in
@[simp]
theorem mem_fieldImage (ι : K →+* R) (a : Multiplicative R) :
    a ∈ fieldImage ι ↔ a.toAdd ∈ Set.range ι := by
  rfl

/-- The subgroup of multiplication characters whose parameters lie in the field. -/
def fieldCharacters (ι : K →+* R) (ψ : AddChar R Circle) (hψ : Continuous ψ) :
    Subgroup (PontryaginDual (Multiplicative R)) :=
  ((RingPontryaginPairing.hom ψ hψ).toMonoidHom.comp
    ι.toAddMonoidHom.toMultiplicative).range

/-- Self-annihilation of a cocompact field parametrizes the characters trivial on it. -/
theorem exists_field_parameter (ι : K →+* R)
    [CompactSpace (Multiplicative R ⧸ fieldImage ι)]
    [T2Space (Multiplicative R ⧸ fieldImage ι)]
    (ψ : AddChar R Circle) (hψ : Continuous ψ)
    (htriv : ∀ k : K, ψ (ι k) = 1)
    (hann : ∀ a : R, (∀ k : K, ψ (a * ι k) = 1) ↔ a ∈ Set.range ι)
    (χ : PontryaginDual (Multiplicative R))
    (hχ : ∀ k : K, χ (Multiplicative.ofAdd (ι k)) = 1) :
    ∃ k : K, RingPontryaginPairing.hom ψ hψ (Multiplicative.ofAdd (ι k)) = χ := by
  have hH : ∀ η ∈ fieldCharacters ι ψ hψ, ∀ a ∈ fieldImage ι, η a = 1 := by
    rintro η ⟨k, rfl⟩ a ⟨l, rfl⟩
    change ψ (ι k.toAdd * ι l.toAdd) = 1
    rw [← map_mul]
    exact htriv _
  have hsep : ∀ a ∉ fieldImage ι, ∃ η ∈ fieldCharacters ι ψ hψ, η a ≠ 1 := by
    intro a ha
    have hn : ¬ ∀ k : K, ψ (a.toAdd * ι k) = 1 := by
      intro h
      exact ha ((mem_fieldImage ι a).mpr ((hann a.toAdd).mp h))
    push Not at hn
    obtain ⟨k, hk⟩ := hn
    refine ⟨RingPontryaginPairing.hom ψ hψ (Multiplicative.ofAdd (ι k)),
      ⟨Multiplicative.ofAdd k, rfl⟩, ?_⟩
    change ψ (ι k * a.toAdd) ≠ 1
    simpa only [mul_comm] using hk
  have hm : χ ∈ fieldCharacters ι ψ hψ :=
    HarmonicAnalysis.CompactQuotientCharacters.mem_of_separates_quotient
      (fieldImage ι) (fieldCharacters ι ψ hψ) hH hsep χ (by
        rintro a ⟨k, rfl⟩
        exact hχ k.toAdd)
  obtain ⟨k, hk⟩ := hm
  exact ⟨k.toAdd, hk⟩

/-- Restriction matching and field-trivial parametrization give the full dual. -/
theorem pairing_surjective (ι : K →+* R)
    [CompactSpace (Multiplicative R ⧸ fieldImage ι)]
    [T2Space (Multiplicative R ⧸ fieldImage ι)]
    (ψ : AddChar R Circle) (hψ : Continuous ψ)
    (htriv : ∀ k : K, ψ (ι k) = 1)
    (hann : ∀ a : R, (∀ k : K, ψ (a * ι k) = 1) ↔ a ∈ Set.range ι)
    (hmatch : ∀ χ : PontryaginDual (Multiplicative R),
      ∃ a : R, ∀ k : K, χ (Multiplicative.ofAdd (ι k)) = ψ (a * ι k)) :
    Function.Surjective (RingPontryaginPairing.hom ψ hψ) := by
  intro χ
  obtain ⟨a, ha⟩ := hmatch χ
  let η := χ / RingPontryaginPairing.hom ψ hψ (Multiplicative.ofAdd a)
  have hη : ∀ k : K, η (Multiplicative.ofAdd (ι k)) = 1 := by
    intro k
    change χ (Multiplicative.ofAdd (ι k)) / ψ (a * ι k) = 1
    rw [ha k, div_self']
  obtain ⟨k, hk⟩ := exists_field_parameter ι ψ hψ htriv hann η hη
  refine ⟨Multiplicative.ofAdd (ι k + a), ?_⟩
  change RingPontryaginPairing.hom ψ hψ
    (Multiplicative.ofAdd (ι k) * Multiplicative.ofAdd a) = χ
  rw [map_mul, hk]
  exact div_mul_cancel χ _

end Langlands.Global.CocompactRingCharacters
