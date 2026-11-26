import Langlands.Global.AdelicFullRationalQuotientProduct
import Langlands.Global.AdelicPrincipalQuotientProduct
import Langlands.Global.AdelicWavePacketAmbientLiftStatement

/-! # Pairing an ambient wave-packet lift against a unitary central character -/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Global

open GroupScheme PositiveRealTorus AdelicGroupPoints
  Langlands.Automorphic.GroupSchemeFunctions

open RestrictionSplitCentre (canonicalComponent canonicalTorus canonicalSubgroup
  canonicalRationalSubgroup positiveCentreEquiv intrinsicCentreHaarMeasure
  positiveCentreHaarMeasure measurePreserving_positiveCentreEquiv)

section Product

variable (F : Type) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G)

local notation "T" => canonicalTorus F G
local notation "i" => canonicalComponent F G
local notation "hi" => RestrictionSplitCentre.canonical_characterRestrict_injective F G
  centralSplitTorusCharacter hG
local notation "hs" => RestrictionSplitCentre.isSplitComponent_canonicalComponent F G
local notation "A" => canonicalSubgroup F G
local notation "Q₁" => NormOneRationalQuotient F G

omit [NumberField F] in
private theorem canonicalTorus_split : IsSplitTorus (T).toGrp := (hs).1.1.1

private def splitIndex : Type := (canonicalTorus_split F G).choose

private instance : Fintype (splitIndex F G) :=
  @Fintype.ofFinite _ (canonicalTorus_split F G).choose_spec.1

private def splitCoordinates : (T).toGrp ≅ splitTorus (Spec (CommRingCat.of F)) (splitIndex F G) :=
  Classical.choice (canonicalTorus_split F G).choose_spec.2

private def centreNormOneProduct : A × Q₁ ≃ₜ RationalQuotient F G :=
  let := RestrictionSplitCentre.canonical_finiteIndex F G hG
  ((positiveCentreEquiv F G hG).symm.toHomeomorph.prodCongr (Homeomorph.refl _)).trans
    (rationalQuotientDecomposition F G T i hi (splitIndex F G) (splitCoordinates F G) (hs).1.2)

private theorem centreNormOneProduct_mk (a : A) (n : normOneSubgroup F G) :
    centreNormOneProduct F G hG (a, LeftCosetSpace.mk (rationalNormOneSubgroup F G) n) =
      LeftCosetSpace.mk (AdelicGroupPoints.rationalSubgroup F G) (a.val * n.val) := by
  let := RestrictionSplitCentre.canonical_finiteIndex F G hG
  change rationalQuotientDecomposition F G T i hi (splitIndex F G) (splitCoordinates F G) (hs).1.2
    ((positiveCentreEquiv F G hG).symm a, LeftCosetSpace.mk (rationalNormOneSubgroup F G) n) = _
  rw [rationalQuotientDecomposition_mk, ← RestrictionSplitCentre.positiveCentreEquiv_coe F G hG,
    ContinuousMulEquiv.apply_symm_apply]

private theorem sigmaFinite_positiveCentreHaarMeasure :
    SigmaFinite (positiveCentreHaarMeasure F G hG) :=
  (positiveCentreEquiv F G hG).toMeasurableEquiv.sigmaFinite_map

private theorem measurePreserving_centreNormOneProduct :
    MeasurePreserving (centreNormOneProduct F G hG)
      ((positiveCentreHaarMeasure F G hG).prod (normOneRationalQuotientHaarMeasure F G))
      (rationalQuotientHaarMeasure F G) := by
  let := RestrictionSplitCentre.canonical_finiteIndex F G hG
  have := sigmaFinite_positiveCentreHaarMeasure F G hG
  have h₁ := (measurePreserving_positiveCentreEquiv F G hG).symm
    (positiveCentreEquiv F G hG).toMeasurableEquiv
  have h₂ := measurePreserving_rationalQuotientDecomposition F G T i hi (splitIndex F G)
    (splitCoordinates F G) (hs).1.2
  have hmeasure : intrinsicCentreHaarMeasure F G hG =
      normalizedPositiveHaarMeasure F G T i hi (splitIndex F G) (splitCoordinates F G) (hs).1.2 :=
    intrinsicPositiveHaarMeasure_eq F G T i hi (splitIndex F G) (splitCoordinates F G) (hs).1.2 _
  rw [← hmeasure] at h₂
  exact h₂.comp (h₁.prod (MeasurePreserving.id _))

end Product

section Pairing

variable {F : Type} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}

private theorem leftInvariant_out {Γ : Subgroup (AdelicGroupPoints F G)}
    {f : AdelicGroupPoints F G → ℂ} (hf : IsLeftInvariantUnder F G Γ f)
    (g : AdelicGroupPoints F G) : f (LeftCosetSpace.mk Γ g).out = f g := by
  let g' := (LeftCosetSpace.mk Γ g).out
  have hg' : LeftCosetSpace.mk Γ g' = LeftCosetSpace.mk Γ g := Quotient.out_eq _
  have hmem : g' * g⁻¹ ∈ Γ := (LeftCosetSpace.mk_eq_mk_iff Γ g g').mp hg'.symm
  simpa only [mul_assoc, inv_mul_cancel, mul_one, g'] using hf (g' * g⁻¹) hmem g

private theorem ambientWavePacketProfile_eq_of_characterLog_eq {m : ℕ}
    (e : (Fin m → ℝ) ≃ₗ[ℝ] RealCharacterParameter F G) (b : (Fin m → ℝ) → ℂ)
    {x y : AdelicGroupPoints F G} (h : characterLog F G x = characterLog F G y) :
    ambientWavePacketProfile e b x = ambientWavePacketProfile e b y := by
  simp only [ambientWavePacketProfile, parameterPower, h]

/-- A pairing against a unitary central character factors on the full principal quotient.
If the central scalar is nonzero, absolute integrability of the two adelic pairings is equivalent. -/
def WavePacketUnitaryCentrePairingStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G)
    {m : ℕ} (e : (Fin m → ℝ) ≃ₗ[ℝ] RealCharacterParameter F G) (b : (Fin m → ℝ) → ℂ)
    (ν : RealCharacterParameter F G) (Θ Φ : AdelicGroupPoints F G → ℂ),
    IsLeftInvariantUnder F G (AdelicGroupPoints.rationalSubgroup F G) Φ →
    (∀ a ∈ canonicalSubgroup F G, ∀ g,
      Φ (a * g) = parameterPower F G (imaginaryParameter F G ν) a * Φ g) →
    IsLeftInvariantUnder F G (canonicalRationalSubgroup F G) Θ →
    let centralScalar := ∫ a : canonicalSubgroup F G,
      ambientWavePacketProfile e b a.val *
        starRingEnd ℂ (parameterPower F G (imaginaryParameter F G ν) a.val)
      ∂(positiveCentreHaarMeasure F G hG)
    let fullPairing (q : RationalQuotient F G) :=
      (ambientWavePacketProfile e b q.out * Θ q.out) * starRingEnd ℂ (Φ q.out)
    let relativePairing (q : NormOneRationalQuotient F G) :=
      Θ (q.out : normOneSubgroup F G).val * starRingEnd ℂ (Φ (q.out : normOneSubgroup F G).val)
    centralScalar ≠ 0 →
    (Integrable fullPairing (rationalQuotientHaarMeasure F G) ↔
      Integrable relativePairing (normOneRationalQuotientHaarMeasure F G)) ∧
    (∫ q, fullPairing q ∂(rationalQuotientHaarMeasure F G)) = centralScalar *
      ∫ q, relativePairing q ∂(normOneRationalQuotientHaarMeasure F G)

/-- Split-centre factorization and absolute convergence for a nonzero central scalar. -/
theorem wavePacketUnitaryCentrePairing : WavePacketUnitaryCentrePairingStatement := by
  intro F _ _ G _ _ hG m e b ν Θ Φ hΦ hcentral hΘ centralScalar fullPairing relativePairing hc
  let chart := centreNormOneProduct F G hG
  let centreMeasure := positiveCentreHaarMeasure F G hG
  have : SigmaFinite centreMeasure := sigmaFinite_positiveCentreHaarMeasure F G hG
  let normOneMeasure := normOneRationalQuotientHaarMeasure F G
  let centreKernel (a : canonicalSubgroup F G) := ambientWavePacketProfile e b a.val *
    starRingEnd ℂ (parameterPower F G (imaginaryParameter F G ν) a.val)
  let f (g : AdelicGroupPoints F G) :=
    (ambientWavePacketProfile e b g * Θ g) * starRingEnd ℂ (Φ g)
  have hf : IsLeftInvariantUnder F G (AdelicGroupPoints.rationalSubgroup F G) f := by
    intro x hx g
    have hx₀ := (characterLog_eq_zero_iff F G x).mpr (rationalSubgroup_le_normOneSubgroup F G hx)
    have hx' := RestrictionSplitCentre.principal_le_rationalSubgroup F G
      (RestrictionSplitCentre.canonicalRestrictionTorus F G)
      (RestrictionSplitCentre.canonicalRestrictionComponent F G) hx
    have hlog : characterLog F G (x * g) = characterLog F G g := by
      rw [characterLog_mul, hx₀, zero_add]
    dsimp only [f]
    rw [ambientWavePacketProfile_eq_of_characterLog_eq e b hlog, hΘ x hx', hΦ x hx]
  have hfactor : fullPairing ∘ chart = fun z => centreKernel z.1 * relativePairing z.2 := by
    funext z
    obtain ⟨a, q⟩ := z
    let n := (q.out : normOneSubgroup F G)
    have hn : LeftCosetSpace.mk (rationalNormOneSubgroup F G) n = q := Quotient.out_eq q
    have hchart : chart (a, q) =
        LeftCosetSpace.mk (AdelicGroupPoints.rationalSubgroup F G) (a.val * n.val) := by
      change centreNormOneProduct F G hG (a, q) = _
      rw [← hn, centreNormOneProduct_mk]
    have ha := RestrictionSplitCentre.subgroup_le_rationalSubgroup F G
      (RestrictionSplitCentre.canonicalRestrictionTorus F G)
      (RestrictionSplitCentre.canonicalRestrictionComponent F G) a.property
    have hlog : characterLog F G (a.val * n.val) = characterLog F G a.val := by
      rw [characterLog_mul, (characterLog_eq_zero_iff F G n.val).mpr n.property, add_zero]
    change f (chart (a, q)).out = centreKernel a * relativePairing q
    rw [hchart, leftInvariant_out hf]
    dsimp only [f, centreKernel, relativePairing]
    rw [ambientWavePacketProfile_eq_of_characterLog_eq e b hlog, hΘ _ ha,
      hcentral _ a.property, map_mul]
    ring
  have hmeasure := measurePreserving_centreNormOneProduct F G hG
  have hcentreIntegral : (∫ a, centreKernel a ∂centreMeasure) ≠ 0 := hc
  have hcentre : Integrable centreKernel centreMeasure := by
    by_contra hn
    exact hcentreIntegral (integral_undef hn)
  constructor
  · rw [← hmeasure.integrable_comp_emb chart.measurableEmbedding, hfactor]
    constructor
    · intro hprod
      have hsections := ((integrable_prod_iff hprod.aestronglyMeasurable).mp hprod).1
      by_contra hrel
      have hzero : centreKernel =ᵐ[centreMeasure] 0 := by
        filter_upwards [hsections] with a ha
        by_contra hne
        apply hrel
        have hinv := ha.const_mul (centreKernel a)⁻¹
        have heq : (fun q => (centreKernel a)⁻¹ * (centreKernel a * relativePairing q)) =
            relativePairing := funext fun q => by rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
        exact heq ▸ hinv
      exact hcentreIntegral (by rw [integral_congr_ae hzero]; simp)
    · exact fun hrelative => hcentre.mul_prod hrelative
  · rw [← hmeasure.integral_comp chart.measurableEmbedding fullPairing]
    change (∫ z, (fullPairing ∘ chart) z ∂(centreMeasure.prod normOneMeasure)) = _
    rw [hfactor, integral_prod_mul]

end Pairing

end Langlands.Global
