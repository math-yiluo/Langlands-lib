import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalConjugationAdapters
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalConjugationSmoothness
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSplitCentralQuotientModulusBound
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalUniformizerHeightSummability
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSplitCentralUniformizerCover

/-! # Assembly of actual split-central integrability from the bound and structural cover -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal Pointwise
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact Langlands.QuotientIntegration
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

section Local

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

omit [LocallyOfFiniteType G.X.hom] in
/-- Dominant integral powers belong to the full actual minimal chamber. -/
theorem uniformizerPowers_mem_rationalMinimalChamber_of_dominant
    (y : cocharacterLattice S)
    (hy : ∀ β : SimpleRoot i ν, 0 ≤ simpleRootPairing i ν β y) :
    uniformizerPowers i (.ofAdd y) ∈ rationalMinimalChamber i ν := by
  apply (mem_rationalMinimalChamber_iff_order i ν _).mpr
  refine ⟨CocharacterUniformizer.latticeSection F S (.ofAdd y), rfl, fun β hβ => ?_⟩
  change 0 ≤ (Plancherel.rationalCharacterValuation S.toGrp
    (CocharacterUniformizer.latticeSection F S (.ofAdd y))).toAdd
      ((rationalCharacters.equivCharacterLattice S).symm β)
  rw [CocharacterUniformizer.rationalCharacterValuation_latticeSection]
  exact hy ⟨β, hβ⟩

/-- The local VIII.3.2 conclusion follows from VIII.3.1 and the actual structural
quotient cover, with volume, summability, smoothness and measurability proved. -/
theorem rationalCuspidalConjugationIntegrability_of_bound_and_uniformizerCover
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {K0 : Subgroup (rationalPoints G)} (hbasis : SimultaneousStandardBasisAt i ν K0)
    {K : OpenSubgroup (rationalPoints G)}
    (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
    {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))
    (hρ : IsClosedSubgroup ρ)
    (s : T.toGrp ⟶ G) (hs : IsSplitComponent s)
    [MeasurableSpace (rationalPoints.map s).range]
    [BorelSpace (rationalPoints.map s).range]
    [MeasurableSpace (LeftQuotient (rationalPoints.map s).range)]
    [BorelSpace (LeftQuotient (rationalPoints.map s).range)]
    {muG : Measure (rationalPoints G)} [muG.IsHaarMeasure]
    {muA : Measure (rationalPoints.map s).range} [muA.IsHaarMeasure]
    [muA.IsMulRightInvariant]
    {muQ : Measure (LeftQuotient (rationalPoints.map s).range)}
    (hQ : IsCompatible (rationalPoints.map s).range muG muA muQ)
    (hbound : RationalCuspidalConjugationBound hKc hPK ρ muG)
    (hcover : RationalSplitCentralUniformizerCover i ν s) :
    RationalCuspidalConjugationIntegrability hKc hPK ρ s hs muG muQ := by
  have : T2Space (rationalPoints G) := rationalPoint_t2Space F G
  have : SecondCountableTopology (rationalPoints G) := rationalPoint_secondCountableTopology F G
  have : muG.IsMulRightInvariant := by
    refine ⟨fun g => ?_⟩
    have h1 : Measure.modularCharacterFun g = 1 := rationalPoints_modularCharacter_eq_one hG g
    rw [Measure.map_right_mul_eq_modularCharacterFun_smul muG g, h1, one_smul]
  obtain ⟨I, hI, ⟨e⟩⟩ := hi.isSplitSubtorus.1.exists_cocharacterCoordinates
  have : Countable (cocharacterLattice S) := e.injective.countable
  let J := {y : cocharacterLattice S //
    (∀ β : SimpleRoot i ν, 0 ≤ simpleRootPairing i ν β y) ∧
      uniformizerPowers i (.ofAdd y) ∈ Plancherel.rationalCommonNormKernel G}
  let a0 : J → rationalMinimalChamberInNormKernel i ν := fun y =>
    ⟨uniformizerPowers i (.ofAdd y.val),
      uniformizerPowers_mem_rationalMinimalChamber_of_dominant y.val y.property.1,
      y.property.2⟩
  let a : J → standardParabolicPoints i ν ∅ :=
    fun y => rationalMinimalChamberToParabolic i ν (a0 y)
  obtain ⟨H, hH, Y, hY, hcover⟩ := hcover
  let Ω : J → Set (LeftQuotient (rationalPoints.map s).range) := fun y =>
    leftQuotientMap (rationalPoints.map s).range ''
      ((H : Set (rationalPoints G)) * {(a y : rationalPoints G)} * Y)
  have hΩcover : ∀ q, ∃ y : J, q ∈ Ω y := by
    intro q
    obtain ⟨y, hy, hker, hq⟩ := hcover q
    exact ⟨⟨y, hy, hker⟩, hq⟩
  have ha : ∀ y : J, a y ∈ rationalParabolicConjugationChamber i ν :=
    fun y => (a0 y).property
  have hcell : ∀ y : J, ∀ q ∈ Ω y, ∃ k ∈ (H : Set (rationalPoints G)), ∃ z ∈ Y,
      q = Quotient.mk _ (k * (a y : rationalPoints G) * z) := by
    rintro y q ⟨g, ⟨v, ⟨k, hk, _, rfl, rfl⟩, z, hz, rfl⟩, rfl⟩
    exact ⟨k, hk, z, hz, rfl⟩
  obtain ⟨C, -, hvol⟩ :=
    exists_rationalSplitCentralQuotient_measure_compact_cell_le_inverse_modulus
      hi hbasis s hs hQ H hH hY
  have hm : ∀ y : J, muQ (Ω y) ≤ ENNReal.ofReal
      (C * (((rationalMinimalModulus i ν (a y) : ℝ≥0) : ℝ))⁻¹) :=
    fun y => hvol y.val y.property.1 (a y).property
  obtain ⟨d, hd⟩ := exists_summable_rationalHeight_uniformizerPowers
    i hi.isSplitSubtorus.1 hi.isSplitSubtorus.2 ρ hρ
  have hsum : Summable (fun y : J => (1 + rationalHeight (F := F) ρ (a y)) ^ (-(d : ℝ))) :=
    hd.comp_injective Subtype.val_injective
  refine ⟨hbound.1, fun f1 hf1 f2 => ?_⟩
  have ht := rationalTranslationWeights K.isOpen hKc hPK ρ
  have h31 : ∀ k ∈ (H : Set (rationalPoints G)), ∀ z ∈ Y,
      ConjugationIntegralBound muG (rationalParabolicConjugationChamber i ν)
        (conjFun k (f1 : rationalPoints G → ℂ))
        (conjFun z⁻¹ (f2 : rationalPoints G → ℂ))
        (rationalConjugationHalfWeight hPK) (rationalHeight (F := F) ρ) := by
    intro k _ z _
    let f1k := Space.translate ht k⁻¹ k⁻¹ f1
    let f2z := Space.translate ht z z f2
    have hf1k : f1k ∈ rationalCuspidalSubmodule hKc hPK ρ := by
      intro I hI muU hmuU x y
      simpa only [f1k, Space.translate_apply, inv_inv, mul_assoc] using
        hf1 I hI muU hmuU (k * x) (y * k⁻¹)
    have hb := (conjugationIntegralBound_iff_rationalChamberBound hKc hPK ρ muG
      (f1k : rationalPoints G → ℂ) (f2z : rationalPoints G → ℂ)).mpr
        (hbound.2 f1k hf1k f2z)
    have hcoe1 : (f1k : rationalPoints G → ℂ) = conjFun k (f1 : rationalPoints G → ℂ) := by
      funext g
      simp only [f1k, Space.translate_apply, conjFun, inv_inv]
    have hcoe2 : (f2z : rationalPoints G → ℂ) = conjFun z⁻¹ (f2 : rationalPoints G → ℂ) := by
      funext g
      simp only [f2z, Space.translate_apply, conjFun, inv_inv]
    rw [hcoe1, hcoe2] at hb
    exact hb
  exact integrable_rationalLeftConjugationPairing_of_conjugationIntegralBound
    hKc hPK ρ s hs muG muQ f1 f2 hΩcover ha hcell
    (finite_rationalConjugates hKc hPK ρ f1 hH)
    (finite_rationalInverseConjugates hKc hPK ρ f2 hY) h31 hm hsum
    (aestronglyMeasurable_rationalLeftConjugationPairing hKc hPK ρ s hs muG f1 f2 muQ)

end Local

/-- The reduction of the closed VIII.3.2 target to VIII.3.1 and the joint
special-compact existence statement. -/
def RationalCuspidalConjugationIntegrabilityReductionStatement : Prop :=
  RationalCuspidalConjugationBoundStatement.{u} →
    JointSpecialCompactBasisExistenceStatement.{u} →
    RationalCuspidalConjugationIntegrabilityStatement.{u}

/-- The conditional VIII.3.2 assembly for the original compatible quotient. -/
theorem rationalCuspidalConjugationIntegrability_of_bound_and_jointSpecialCompactBasis :
    RationalCuspidalConjugationIntegrabilityReductionStatement.{u} := by
  intro hbound hjoint F _ _ _ _ G _ _ hG S i hi ν hν K0 hbasis K hKc hPK N _ ρ hρ T s hs
    _ _ _ _ muG hmuG muA _ _ muQ hQ
  let := hmuG
  exact rationalCuspidalConjugationIntegrability_of_bound_and_uniformizerCover hG hi hbasis
    hKc hPK ρ hρ s hs hQ (hbound F G hG S i hi ν hν K0 hbasis K hKc hPK N ρ hρ muG hmuG)
    (rationalSplitCentralUniformizerCover_of_jointSpecialCompactBasis hjoint hG hi hν hs)

end Langlands.HarishChandraSchwartz
