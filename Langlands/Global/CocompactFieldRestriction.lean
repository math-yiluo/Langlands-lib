import Langlands.Global.CocompactRingCharacters
import Langlands.HarmonicAnalysis.CompactCharacterRange

/-! # Matching character restrictions to a cocompact field -/

noncomputable section

open Set

universe u v

namespace Langlands.Global.CocompactFieldRestriction

open CocompactRingCharacters

variable {K : Type u} [Field K] [TopologicalSpace K] [DiscreteTopology K]
variable {R : Type v} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- A field map with the discrete topology on its source. -/
def discreteEmbedding (ι : K →+* R) : Multiplicative K →ₜ* Multiplicative R where
  toMonoidHom := ι.toAddMonoidHom.toMultiplicative
  continuous_toFun := continuous_of_discreteTopology

/-- Restrict a multiplication character to the discrete field. -/
def restriction (ι : K →+* R) (ψ : AddChar R Circle) (hψ : Continuous ψ) :
    Multiplicative R →ₜ* PontryaginDual (Multiplicative K) :=
  (PontryaginDual.map (discreteEmbedding ι)).comp (RingPontryaginPairing.hom ψ hψ)

/-- The restriction pairing descends to the quotient by the field. -/
def quotientRestriction (ι : K →+* R) (ψ : AddChar R Circle) (hψ : Continuous ψ)
    (htriv : ∀ k : K, ψ (ι k) = 1) :
    (Multiplicative R ⧸ fieldImage ι) →ₜ* PontryaginDual (Multiplicative K) where
  toMonoidHom := QuotientGroup.lift (fieldImage ι) (restriction ι ψ hψ).toMonoidHom (by
    rintro a ⟨k, rfl⟩
    apply PontryaginDual.ext
    intro l
    change ψ (ι k.toAdd * ι l.toAdd) = 1
    rw [← map_mul, htriv])
  continuous_toFun := (QuotientGroup.isQuotientMap_mk (fieldImage ι)).continuous_iff.mpr
    (restriction ι ψ hψ).continuous

@[simp]
theorem quotientRestriction_mk (ι : K →+* R) (ψ : AddChar R Circle) (hψ : Continuous ψ)
    (htriv : ∀ k : K, ψ (ι k) = 1) (a : Multiplicative R) (k : Multiplicative K) :
    quotientRestriction ι ψ hψ htriv (QuotientGroup.mk a) k = ψ (a.toAdd * ι k.toAdd) := rfl

/-- Evaluation characters of the full dual of a discrete field. -/
def evaluationHom : Multiplicative K →* PontryaginDual (PontryaginDual (Multiplicative K)) where
  toFun k :=
    { toFun := fun χ => χ k
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      continuous_toFun := by
        change Continuous (fun χ : Multiplicative K →ₜ* Circle => χ k)
        exact continuous_eval_const k }
  map_one' := by
    apply PontryaginDual.ext
    intro χ
    exact map_one χ
  map_mul' k l := by
    apply PontryaginDual.ext
    intro χ
    exact map_mul χ k l

/-- Every character of the discrete field is realized by the multiplication pairing. -/
theorem quotientRestriction_surjective (ι : K →+* R)
    [CompactSpace (Multiplicative R ⧸ fieldImage ι)]
    [T2Space (Multiplicative R ⧸ fieldImage ι)]
    (ψ : AddChar R Circle) (hψ : Continuous ψ) (hne : ψ ≠ 1)
    (htriv : ∀ k : K, ψ (ι k) = 1) :
    Function.Surjective (quotientRestriction ι ψ hψ htriv) := by
  classical
  apply HarmonicAnalysis.CompactCharacterRange.surjective_of_character_detection
    (quotientRestriction ι ψ hψ htriv) (evaluationHom (K := K)).range
  · intro x y hxy
    obtain ⟨k, hk⟩ : ∃ k : Multiplicative K, x k ≠ y k := by
      by_contra! h
      exact hxy (PontryaginDual.ext h)
    exact ⟨⟨evaluationHom k, ⟨k, rfl⟩⟩, hk⟩
  · rintro χ ⟨k, rfl⟩ hk
    have hk0 : k.toAdd = 0 := by
      by_contra hk0
      apply hne
      apply AddChar.ext
      intro y
      have hz := congrArg
        (fun η : PontryaginDual (Multiplicative R ⧸ fieldImage ι) =>
          η (QuotientGroup.mk (Multiplicative.ofAdd (ι k.toAdd⁻¹ * y)))) hk
      change ψ ((ι k.toAdd⁻¹ * y) * ι k.toAdd) = 1 at hz
      have hm : (ι k.toAdd⁻¹ * y) * ι k.toAdd = y := by
        calc
          (ι k.toAdd⁻¹ * y) * ι k.toAdd = (ι k.toAdd⁻¹ * ι k.toAdd) * y := by ring
          _ = y := by rw [← map_mul, inv_mul_cancel₀ hk0, map_one, one_mul]
      simpa only [hm, AddChar.one_apply] using hz
    have hk1 : k = 1 := congrArg Multiplicative.ofAdd hk0
    rw [hk1, map_one]

/-- Match the restriction of an arbitrary continuous ring character. -/
theorem exists_parameter (ι : K →+* R)
    [CompactSpace (Multiplicative R ⧸ fieldImage ι)]
    [T2Space (Multiplicative R ⧸ fieldImage ι)]
    (ψ : AddChar R Circle) (hψ : Continuous ψ) (hne : ψ ≠ 1)
    (htriv : ∀ k : K, ψ (ι k) = 1)
    (χ : PontryaginDual (Multiplicative R)) :
    ∃ a : R, ∀ k : K, χ (Multiplicative.ofAdd (ι k)) = ψ (a * ι k) := by
  obtain ⟨q, hq⟩ := quotientRestriction_surjective ι ψ hψ hne htriv
    (χ.comp (discreteEmbedding ι))
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨a.toAdd, fun k => ?_⟩
  exact (congrArg (fun η : PontryaginDual (Multiplicative K) => η (Multiplicative.ofAdd k)) hq).symm

end Langlands.Global.CocompactFieldRestriction
