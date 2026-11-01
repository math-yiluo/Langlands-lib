import Langlands.Representation.RankinSelberg.AdjacentRankSectionSpanning
import Langlands.Representation.RankinSelberg.AdjacentRankNormalizedSection
import Langlands.Representation.Induction.Equivalences
import Langlands.Representation.Induction.CharacterTwistProof
import Langlands.Representation.Induction.InverseTranspose
import Langlands.Representation.Parabolic.QuotientCompactProof
import Langlands.Group.GL.CompactOpen
import Langlands.Topology.CompactOpen.NeighborhoodBasis

/-! Surjectivity of the actual normalized rectangular-section tensor map. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Matrix Induction
open scoped TensorProduct

universe uF uV

section General

variable {K : Type uF} [Field K] [TopologicalSpace K]
  [IsTopologicalDivisionRing K] [T2Space K] {r : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

private abbrev P := (adjacentRankLowerShape r).oppositeParabolic K
private abbrev a : P (K := K) (r := r) →* GeneralLinear (r + 1) K :=
  adjacentRankLowerLargeProjection

variable [MeasurableSpace (GeneralLinear (r + 1) K)]
  [OpensMeasurableSpace (GeneralLinear (r + 1) K)]
  (μ : Measure (GeneralLinear (r + 1) K)) [IsFiniteMeasureOnCompacts μ]
  (ρ : Representation ℂ (GeneralLinear (r + 1) K) V) (hρ : IsSmooth ρ)
  (ξ : GeneralLinear (r + 1) K →* ℂˣ)
  (hξ : IsLocallyConstant (fun h => (ξ h : ℂ)))
  (hμ : ∀ q : P (K := K) (r := r),
    MeasurePreserving (fun h : GeneralLinear (r + 1) K => h * a q) μ μ)

private abbrev τ :=
  adjacentRankCompactSectionRepresentation (P (K := K) (r := r)) a ρ ξ
    adjacentRankUnitCharacter

/-- Compactness of the quotient promotes the trivial-character compact spanning
theorem to surjectivity onto the whole smooth induction. -/
theorem adjacentRankLowerSectionTensor_unit_surjective [μ.IsOpenPosMeasure]
    [CompactSpace (LeftQuotient (P (K := K) (r := r)))]
    (hbasis : ∀ O : Set (GeneralLinear (r + 2) K), IsOpen O → 1 ∈ O →
      ∃ J : OpenSubgroup (GeneralLinear (r + 2) K),
        IsCompact (J : Set (GeneralLinear (r + 2) K)) ∧
        (J : Set (GeneralLinear (r + 2) K)) ⊆ O) :
    Function.Surjective
      (adjacentRankLowerSectionTensor μ ρ hρ ξ hξ hμ adjacentRankUnitCharacter) := by
  intro f
  obtain ⟨fc, hfc⟩ := (compactInclusion_bijective_of_compactSpace P (τ ρ ξ)).2 f
  obtain ⟨t, ht⟩ :=
    adjacentRankCompactSectionTensor_covers_compact μ ρ hρ ξ hξ hμ hbasis fc
  exact ⟨t, ht.trans hfc⟩

/-- Twisting the trivial outer-character inducing action gives the desired action,
through the identity map on the original module. -/
def adjacentRankLowerOuterTwistCoordinates
    (θ : SmoothCharacter ℂ (GeneralLinear (r + 2) K)) :
    (twist (θ.toMonoidHom.comp (P (K := K) (r := r)).subtype) (τ ρ ξ)).Equiv
      (adjacentRankCompactSectionRepresentation P a ρ ξ θ) :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ V) (by
    intro q
    apply LinearMap.ext
    intro v
    change (θ.toMonoidHom q.val : ℂ) •
        (((1 : GeneralLinear (r + 2) K →* ℂˣ) q.val * (ξ (a q))⁻¹ : ℂˣ) : ℂ) •
          ρ (a q) v =
      ((θ.toMonoidHom q.val * (ξ (a q))⁻¹ : ℂˣ) : ℂ) • ρ (a q) v
    simp only [MonoidHom.one_apply, one_mul, Units.val_mul, smul_smul])

/-- Character multiplication on actual smooth sections, followed by the identity
coordinates on the inducing module. -/
def adjacentRankLowerOuterTwist
    (θ : SmoothCharacter ℂ (GeneralLinear (r + 2) K)) :
    SmoothFunctions P (τ ρ ξ) ≃ₗ[ℂ]
      SmoothFunctions P (adjacentRankCompactSectionRepresentation P a ρ ξ θ) :=
  (smoothInductionTwistEquiv P θ (τ ρ ξ)).toLinearEquiv.trans
    (smoothInducedEquiv P (adjacentRankLowerOuterTwistCoordinates ρ ξ θ)).toLinearEquiv

omit [T2Space K] [MeasurableSpace (GeneralLinear (r + 1) K)]
  [OpensMeasurableSpace (GeneralLinear (r + 1) K)] in
@[simp] theorem adjacentRankLowerOuterTwist_eval
    (θ : SmoothCharacter ℂ (GeneralLinear (r + 2) K))
    (f : SmoothFunctions P (τ ρ ξ)) (g : GeneralLinear (r + 2) K) :
    eval P _ (adjacentRankLowerOuterTwist ρ ξ θ f) g =
      (θ.toMonoidHom g : ℂ) • eval P (τ ρ ξ) f g := rfl

/-- Character multiplication commutes with the complete tensor-section map. -/
theorem adjacentRankLowerOuterTwist_tensor
    (θ : SmoothCharacter ℂ (GeneralLinear (r + 2) K))
    (t : TensorProduct ℂ (adjacentRankCompactTests (r + 1) K) V) :
    adjacentRankLowerOuterTwist ρ ξ θ
        (adjacentRankLowerSectionTensor μ ρ hρ ξ hξ hμ adjacentRankUnitCharacter t) =
      adjacentRankLowerSectionTensor μ ρ hρ ξ hξ hμ θ t := by
  induction t using TensorProduct.inductionOn with
  | tmul Φ v =>
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change (θ.toMonoidHom g : ℂ) •
        ((adjacentRankUnitCharacter.toMonoidHom g : ℂ) •
          adjacentRankCompactAverage μ ρ hρ ξ hξ Φ v g) =
      (θ.toMonoidHom g : ℂ) • adjacentRankCompactAverage μ ρ hρ ξ hξ Φ v g
    simp [adjacentRankUnitCharacter]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Every outer smooth character has a surjective rectangular-section tensor map. -/
theorem adjacentRankLowerSectionTensor_surjective [μ.IsOpenPosMeasure]
    [CompactSpace (LeftQuotient (P (K := K) (r := r)))]
    (hbasis : ∀ O : Set (GeneralLinear (r + 2) K), IsOpen O → 1 ∈ O →
      ∃ J : OpenSubgroup (GeneralLinear (r + 2) K),
        IsCompact (J : Set (GeneralLinear (r + 2) K)) ∧
        (J : Set (GeneralLinear (r + 2) K)) ⊆ O)
    (θ : SmoothCharacter ℂ (GeneralLinear (r + 2) K)) :
    Function.Surjective (adjacentRankLowerSectionTensor μ ρ hρ ξ hξ hμ θ) := by
  intro f
  obtain ⟨t, ht⟩ :=
    adjacentRankLowerSectionTensor_unit_surjective μ ρ hρ ξ hξ hμ hbasis
      ((adjacentRankLowerOuterTwist ρ ξ θ).symm f)
  refine ⟨t, ?_⟩
  rw [← adjacentRankLowerOuterTwist_tensor, ht, LinearEquiv.apply_symm_apply]

end General

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Inverse transpose takes a compact integral-group cover for the upper quotient
to a compact cover for the actual opposite quotient, in every block shape. -/
theorem oppositeParabolicQuotientCompact (T : F.TopologicalData)
    {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    CompactSpace (LeftQuotient (B.oppositeParabolic F.Carrier)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hcover :
      (fun g => quotientMap (B.oppositeParabolic F.Carrier)
        (GeneralLinear.inverseTranspose n F.Carrier g)) ''
        (GeneralLinear.Iwasawa.integralRange (ValuativeRel.valuation F.Carrier) n :
          Set (GeneralLinear n F.Carrier)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    induction x using Quotient.inductionOn with
    | h g =>
      have hg := Set.mem_univ
        (quotientMap (B.parabolic F.Carrier)
          (GeneralLinear.inverseTranspose n F.Carrier g))
      rw [← Parabolic.quotientMap_image_integralRange T B] at hg
      obtain ⟨k, hk, hkg⟩ := hg
      refine ⟨k, hk, Quotient.sound ?_⟩
      apply QuotientGroup.rightRel_apply.mpr
      have hr : GeneralLinear.inverseTranspose n F.Carrier g * k⁻¹ ∈
          B.parabolic F.Carrier :=
        QuotientGroup.rightRel_apply.mp (Quotient.exact hkg)
      have ho := (B.inverseTranspose_mem_oppositeParabolic_iff F.Carrier _).mpr hr
      simpa only [map_mul, map_inv, GeneralLinear.inverseTranspose_involutive] using ho
  constructor
  rw [← hcover]
  exact (Parabolic.isCompact_integralRange T n).image
    (continuous_quotient_mk'.comp (GeneralLinear.continuous_inverseTranspose n F.Carrier))

local instance sectionSurjectivityTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance sectionSurjectivityValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance sectionSurjectivityLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance sectionSurjectivityT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance sectionSurjectivityGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance sectionSurjectivityGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

variable {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
  (χ : Quasicharacter F.Carrier)

/-- Every vector of the exact canonical normalized opposite-parabolic induction
comes from the original compact-test/vector algebraic tensor product. -/
theorem adjacentRankNormalizedSectionTensor_surjective (hσ : IsSmooth σ) :
    Function.Surjective (adjacentRankNormalizedSectionTensor F σ χ hσ) := by
  let := oppositeParabolicQuotientCompact F F.canonicalTopologicalData
    (adjacentRankLowerShape r)
  have hbasis : ∀ O : Set (GeneralLinear (r + 2) F.Carrier), IsOpen O → 1 ∈ O →
      ∃ J : OpenSubgroup (GeneralLinear (r + 2) F.Carrier),
        IsCompact (J : Set (GeneralLinear (r + 2) F.Carrier)) ∧
        (J : Set (GeneralLinear (r + 2) F.Carrier)) ⊆ O := by
    intro O hO h1
    let J := F.canonicalTopologicalData.generalLinearCompactOpen (r + 2) O
      (hO.mem_nhds h1)
    exact ⟨J.val, J.property⟩
  have hs := adjacentRankLowerSectionTensor_surjective
    (generalLinearHaar F.Carrier r) σ hσ
    (adjacentRankDeterminantWeight F.canonicalTopologicalData χ
      (r + 1) ((r + 2 : ℕ) / 2)).toMonoidHom
    (adjacentRankDeterminantWeight_locallyConstant F.canonicalTopologicalData χ
      (r + 1) ((r + 2 : ℕ) / 2))
    (fun q => measurePreserving_mul_right (generalLinearHaar F.Carrier r)
      (adjacentRankLowerLargeProjection q)) hbasis
    (adjacentRankDeterminantWeight F.canonicalTopologicalData χ
      (r + 2) ((r + 1 : ℕ) / 2))
  exact (smoothInducedEquiv _
    (adjacentRankLowerInducingCoordinates F σ χ).symm).toLinearEquiv.surjective.comp hs

end Padic

end Langlands.RankinSelberg
