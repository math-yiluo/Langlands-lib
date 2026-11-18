import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitJacquetContraction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitConstantTermCompactBounds
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitConstantTermPolynomialGrowth

/-! # Actual orbit positive decay reduced to the upper Xi and shifted growth inputs -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
  (I : Finset (RationalPointFamily.SimpleRoot i ν))
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
  {K0 : Subgroup (rationalPoints G)} (hK0c : IsCompact (K0 : Set (rationalPoints G)))
  (hbasis : SimultaneousStandardBasisAt i ν K0)
  (hcover : StandardLeviCartanCovering F i ν (RationalPointFamily.rootSet i ν I) K0)

set_option hygiene false in
local notation "𝐌" => standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)]
  (mu : Measure (𝐌 ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)
  (J : Finset (RationalPointFamily.SimpleRoot i ν))
  {q : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν (RationalPointFamily.rootSet i ν J) A q)
  {B : Set (Subgroup (rationalPoints G))} (hB : CompactOpenNormalBasis K0 B)
  (hmem : ∀ L ∈ B, StandardParabolicBasisMember i ν (RationalPointFamily.rootSet i ν J) q L)
  (hM' : IsIwasawaPair
    ((standardParabolicPoints i ν ∅).subgroupOf
      (standardLeviPoints i ν (RationalPointFamily.rootSet i ν J)))
    ((K : Subgroup (rationalPoints G)).subgroupOf
      (standardLeviPoints i ν (RationalPointFamily.rootSet i ν J))))

section PolynomialGrowthInput

variable [BorelSpace (𝐌 ⧸ C)]

include hK0c hbasis hcover hB hmem in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
/-- All actual split-decay input except the shifted-chamber polynomial
estimate is derived from the original data and the separately owned
upper Xi statement. In particular the strict point, full-orbit uniform
annihilators and weighted compact bounds are supplied here. -/
theorem hasRationalSplitDecayInput_rationalOrbit_of_polynomialBound
    (hupper : RationalXiUpperBoundStatement.{u})
    {ζ : cocharacterLattice S}
    (hζ : IsStandardCocharacter i ν (RationalPointFamily.rootSet i ν J) ζ)
    {n : ℕ} [Nonempty (Fin n)] (ρ : MatrixRepresentation G (Fin n))
    (Φ : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π)
    (hpoly : HasRationalConstantTermPolynomialBound hG hi hν hKc hM' ρ
      (rationalOrbitConstantTerm hG hi hν I hKc hPK π C hC mu hsq J hA Φ)) :
    HasRationalSplitDecayInput hG hi hν hKc hM' hA ρ
      (rationalOrbitConstantTerm hG hi hν I hKc hPK π C hC mu hsq J hA Φ) := by
  obtain ⟨c, hc⟩ := hA.exists_cocharacter_lift i ν hi hζ
  have hcz : RealTorusSpace.cocharacterMapInt (Additive.ofMul q : A ⟶ S) c = ζ :=
    congrArg Additive.ofMul hc
  let x := CocharacterUniformizer.latticeSection F A (.ofAdd c)
  have hx : x ∈ CocharacterUniformizer.CAstrict F A
      (standardParabolicComponentCharacters i ν (RationalPointFamily.rootSet i ν J) q) := by
    refine ⟨⟨.ofAdd c, rfl⟩, ?_⟩
    rintro _ ⟨α, hα, rfl⟩
    apply CocharacterUniformizer.characterNorm_latticeSection_lt_one
    rw [latticePairing_componentCharacterRestriction]
    change 0 < latticePairing S α
      (RealTorusSpace.cocharacterMapInt (Additive.ofMul q : A ⟶ S) c)
    rw [hcz]
    exact hζ.2.2 α hα.1 hα.2
  refine ⟨x, ?_, ?_, ?_, ?_, hpoly⟩
  · intro β hβ
    rw [eval_rationalComponentH0_latticeSection, hcz, hζ.2.1 β hβ, Int.cast_zero]
  · rintro α ⟨hα, hαJ⟩
    rw [eval_rationalComponentH0_latticeSection, hcz]
    exact_mod_cast hζ.2.2 α hα hαJ
  · exact hasUniformSplitAnnihilators_rationalOrbitConstantTerm_of_xiUpperBound
      hG hi hν I hKc hPK hK0c hbasis hcover π C hC mu hsq J hA hB hmem hupper hζ x hx Φ
  · exact rationalOrbitConstantTerm_uniformWeightedCompactBounds
      hG hi hν I J hKc hPK hA hζ hB hmem π C hC mu hsq hM' Φ

include hK0c hbasis hcover hB hmem in
/-- The actual full-orbit positive constant-term decay follows from the
separately owned upper Xi statement and shifted-chamber polynomial bound.
The other analytic and algebraic split-decay inputs are derived, with the
full closed region and every original orbit parameter retained. -/
theorem rationalOrbitPositiveDecay_of_polynomialBound
    (hupper : RationalXiUpperBoundStatement.{u})
    {ζ : cocharacterLattice S}
    (hζ : IsStandardCocharacter i ν (RationalPointFamily.rootSet i ν J) ζ)
    (hcover0 : StandardLeviCartanCovering F i ν ∅ K0)
    {n : ℕ} [Nonempty (Fin n)] (ρ : MatrixRepresentation G (Fin n))
    (hρ : IsClosedSubgroup ρ)
    (Φ : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π)
    (hpoly : HasRationalConstantTermPolynomialBound hG hi hν hKc hM' ρ
      (rationalOrbitConstantTerm hG hi hν I hKc hPK π C hC mu hsq J hA Φ))
    (N : Seminorm ℝ (RealTorusSpace.V S)) (hN : ∀ v, N v = 0 → v = 0) :
    HasRationalPositivePartDecay hG hi hν N (RationalPointFamily.rootSet i ν J)
      (fun ω m => rationalOrbitPositiveConstantTerm hG hi hν I hKc hPK π C hC mu hsq J hA Φ ω
        (minimalLeviInclusion hG hi hν _ m))
      (fun m => rationalLeviXi hKc hM' (minimalLeviInclusion hG hi hν _ m)) := by
  have hinput := hasRationalSplitDecayInput_rationalOrbit_of_polynomialBound
    hG hi hν I hKc hPK hK0c hbasis hcover π C hC mu hsq J hA hB hmem hM'
      hupper hζ ρ Φ hpoly
  have h := hasRationalPositivePartDecay_of_splitInput
    hG hi hν (RationalPointFamily.rootSet_subset i ν J) K.isOpen hKc hM' hA
    hK0c hcover0 N hN ρ hρ hinput
  simpa only [rationalOrbitPositiveConstantTerm] using h

end PolynomialGrowthInput

/-- The upper Xi estimate and the exact uniform constant-term threshold
together imply the original positive constant-term decay proposition. -/
def RationalOrbitPositiveDecayReductionStatement : Prop :=
  RationalXiUpperBoundStatement.{u} →
  RationalOrbitConstantTermThresholdStatement hG hi hν I hKc hPK π C hC mu hsq J hA →
  RationalOrbitPositiveConstantTermDecayStatement hG hi hν I hKc hPK π C hC mu hsq J hA hM'

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
/-- Discharge all analytic inputs to the exact decay proposition except the
upper Xi statement and the full-chamber threshold. -/
theorem rationalOrbitPositiveDecay_of_xiUpperBound_and_threshold :
    RationalOrbitPositiveDecayReductionStatement
      hG hi hν I hKc hPK π C hC mu hsq J hA hM' := by
  intro hupper hthreshold
  unfold RationalOrbitPositiveConstantTermDecayStatement
  intro hBorel ζ hζ K₁ B₁ hK₁o hK₁c hB₁ hmem₁ hbasis₁ hcartan hcovers N hN Φ
  let := hG.smooth
  let := hG.connectedSpace
  obtain ⟨n, ρ, hρ⟩ := exists_isClosedSubgroup_fin_succ G
  have hpoly := hasRationalOrbitConstantTermPolynomialBounds_of_threshold
    hG hi hν I hKc hPK π C hC mu hsq J hA hM' hupper hthreshold hζ
    hK₁o hK₁c hB₁ hmem₁ hbasis₁ hcartan hcovers ρ hρ Φ
  exact rationalOrbitPositiveDecay_of_polynomialBound hG hi hν I hKc hPK hK₁c hbasis₁
    (hcovers _ (RationalPointFamily.rootSet_subset i ν I)) π C hC mu hsq J hA hB₁ hmem₁
    hM' hupper hζ (hcovers ∅ (Set.empty_subset _)) ρ hρ Φ hpoly N hN

end Langlands.HarishChandraSchwartz
