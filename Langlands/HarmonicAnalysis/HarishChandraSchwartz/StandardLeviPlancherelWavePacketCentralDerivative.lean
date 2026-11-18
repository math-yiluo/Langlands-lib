import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviPlancherelWavePacketRegularity
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitSectionLevelCentralDecay
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviOriginalOrbitXiBound
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.BoundedCartanPacketControl

/-! # Central-direction derivative bounds for the source-normalized standard-Levi packet -/

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Plancherel Langlands.Aubert.General Langlands.Induction
open Langlands.BruhatTits.SpecialCompact
open Langlands.Plancherel.UnramifiedOperatorFamily
open Langlands.Plancherel.DynamicOppositeStandardIntertwining
open Langlands.Plancherel.DynamicOppositeCanonicalScalar
open Langlands.Plancherel.RationalDynamicSource Langlands.Plancherel.RationalPlancherelDensity

namespace Langlands.HarishChandraSchwartz

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2
  rationalWeightsIsAffine rationalWeightsTopology rationalWeightsTopologicalGroup
  rationalWeightsT2Field rationalWeightsLocallyCompact rationalWeightsMeasurableSpace
  rationalWeightsBorelSpace rationalInducedSecondCountable rationalInducedT2
  rationalInducedNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (RationalPointFamily.SimpleRoot i ν))
  {ζ : cocharacterLattice S}
  (hζ : IsStandardCocharacter i ν (RationalPointFamily.rootSet i ν I) ζ)

set_option hygiene false in
local notation "χ" => CommGroupScheme.groupHom ζ ≫ i
set_option hygiene false in
local notation "MS" => parameterScheme (CommGroupScheme.groupHom ζ ≫ i)
set_option hygiene false in
local notation "hMS" => parameterScheme_isConnectedReductive (CommGroupScheme.groupHom ζ ≫ i) hG
set_option hygiene false in
local notation "νL" => normCharacters (CommGroupScheme.groupHom ζ ≫ i)
set_option hygiene false in
local notation "νM" => RationalPointFamily.leviRationalNormCharacters i ν I
set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x}

set_option hygiene false in
local notation "𝐋" => Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I)

local instance standardLeviPacketCentralDerivativeAffineHom : IsAffineHom 𝐋.X.hom :=
  leviScheme_isAffineHom i ν (RationalPointFamily.rootSet i ν I)
local instance standardLeviPacketCentralDerivativeAffine : IsAffine 𝐋.X.left :=
  isAffine_of_isAffineHom 𝐋.X.hom
local instance standardLeviPacketCentralDerivativeFiniteType : LocallyOfFiniteType 𝐋.X.hom :=
  leviScheme_locallyOfFiniteType i ν (RationalPointFamily.rootSet i ν I)
local instance standardLeviPacketCentralDerivativeTopology : TopologicalSpace (rationalPoints 𝐋) :=
  rationalPointTopology F 𝐋.X
local instance standardLeviPacketCentralDerivativeNonarchimedean : NonarchimedeanGroup (rationalPoints 𝐋) :=
  rationalPoints_nonarchimedeanGroup 𝐋

variable {T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine T.X.left]
  (s : T.toGrp ⟶ 𝐋) (hs : IsSplitComponent s)
  (hindex : (RenardCartan.splitValuationImage s).FiniteIndex)

set_option hygiene false in
local notation "CM" => rationalLeviSplitCenter I s
set_option hygiene false in
local notation "hCM" => rationalLeviSplitCenter_le_center I s hs

-- Both instances follow from centrality; explicit binders make typeclass synthesis inferable.
variable [(CM).Normal] [(rationalPoints.map s).range.Normal]

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  [MeasurableSpace (𝐌 ⧸ CM)] [BorelSpace (𝐌 ⧸ CM)]
  (mu : Measure (𝐌 ⧸ CM)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup CM hCM π.obj.representation mu)

set_option hygiene false in
local notation "Aπ" => SmoothRep.pullback (standardLeviDynamicHomeomorph hG hi hν I hζ) π.obj
set_option hygiene false in
local notation "Oπ" => discreteSeriesOrbit CM hCM mu νM (discreteSeriesClass CM hCM mu π hsq)

variable
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (Ks : OpenSubgroup (RationalPoint F G.X))
  (hKs : IsCompact (Ks : Set (RationalPoint F G.X)))
  (hPKs : ∀ g : RationalPoint F G.X,
    ∃ p : parabolic χ, ∃ k : Ks, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (hOppKs : ∀ g : RationalPoint F G.X,
    ∃ p : oppositeParabolic χ, ∃ k : Ks,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (p : ForwardContinuation χ hRefl hCST hG Ks hKs hPKs hOppKs Aπ)
  (qrev : ReverseContinuation χ hRefl hCST hG Ks hKs hPKs hOppKs Aπ)
  {DForward DReverse : Set (unramifiedCharacters νL)}
  (hDForward : IsOpen DForward) (hneForward : DForward.Nonempty)
  (hDForwardΩ : DForward ⊆ forwardFullDomainRegion χ Ks hKs Aπ)
  (hDReverse : IsOpen DReverse) (hneReverse : DReverse.Nonempty)
  (hDReverseΩ : DReverse ⊆ reverseFullDomainRegion χ Ks hKs Aπ)
  {D : Set (unramifiedCharacters νL)}
  (hD : IsOpen D) (hne : D.Nonempty)
  (hirr : ∀ z ∈ D,
    (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
      (leviNormCharacters χ) (parameterTransport χ z) Aπ).IsIrreducible)

set_option hygiene false in
local notation "jP" => conditionalCanonicalRationalScalar χ hRefl hCST hG Ks hKs hPKs hOppKs Aπ
  p qrev hneForward hDForwardΩ hneReverse hDReverseΩ hne hirr

variable (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹)
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))

set_option hygiene false in
local notation "W" => standardLeviPlancherelWeight hG hi hν I hζ π CM hCM mu hsq hRefl hCST
  Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ
  hD hne hirr hreg
set_option hygiene false in
local notation "rhoX" => standardLeviUnitaryUnramifiedCharacterHaar I s hs hindex
set_option hygiene false in
local notation "omegaπ" => discreteSeriesClass CM hCM mu π hsq
set_option hygiene false in
local notation "packet" => standardLeviPlancherelWavePacket hG hi hν I hζ π CM hCM mu hsq
  hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ hDReverse
  hneReverse hDReverseΩ hD hne hirr hreg hKc hPK rhoX


set_option hygiene false in
local notation "decomp" => isSemidirectDecomposition_standard hG hi hν
  (RationalPointFamily.rootSet_subset i ν I)
set_option hygiene false in
local notation "closedU" => isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)
set_option hygiene false in
local notation "closedP" => isClosed_standardParabolicPoints_rootSet hG hi hν I
set_option hygiene false in
local notation "normContinuous" => RationalPointFamily.continuous_leviRationalNormCharacters i ν I
set_option hygiene false in
local notation "projectionContinuous" => continuous_projection_standard hG hi hν
  (RationalPointFamily.rootSet_subset i ν I) _
set_option hygiene false in
local notation "factorization" =>
  factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
set_option hygiene false in
local notation "coordinates" => (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv
set_option hygiene false in
local notation "SectionLevel" => OrbitSectionLevel νM π coordinates decomp closedU K closedP
  hKc normContinuous projectionContinuous factorization
set_option hygiene false in
local notation "includeLevel" => OrbitSectionLevel.toSections νM π coordinates decomp closedU K
  closedP hKc normContinuous projectionContinuous factorization
set_option hygiene false in
local notation "DerivativeIndex" => List (Fin (rationalImageRank 𝐋)) ×
  Module.Dual ℂ (ProductInducedCompactPicture decomp K π.obj)
set_option hygiene false in
local notation "inputSeminorms" => OrbitSectionLevel.seminormFamily νM π coordinates decomp closedU K
  closedP hKc normContinuous projectionContinuous factorization

/-- At each input level and order, finitely many original input derivatives
control the original packet in the ambient central valuation directions. -/
def StandardLeviPacketCentralDerivativeEstimates : Prop :=
  letI := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
  ∀ (H : OpenSubgroup (rationalPoints G)), H ≤ K → ∀ r : ℝ,
    ∃ t : Finset DerivativeIndex, ∃ c : ℝ≥0,
      ∀ (q : SectionLevel H) (g : rationalPoints G),
        ‖packet (includeLevel H q) g‖ ≤
          (c : ℝ) * (t.sup (inputSeminorms H)) q * rationalXi hKc hPK g *
            (1 + ‖rationalValuationCoordinates G hG g‖) ^ (-r)

set_option hygiene false in
local notation "centralEstimates" => StandardLeviPacketCentralDerivativeEstimates hG hi hν I hζ
  s hs hindex π mu hsq hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ
  hDReverse hneReverse hDReverseΩ hD hne hirr hreg hKc hPK

set_option hygiene false in
local notation "rootsI" => RationalPointFamily.rootSet i ν I

variable {K0 : Subgroup (rationalPoints G)} (hK0c : IsCompact (K0 : Set (rationalPoints G)))
  (hbasis : SimultaneousStandardBasisAt i ν K0)
  (hcover : StandardLeviCartanCovering F i ν rootsI K0)

set_option hygiene false in
local notation "unimodular" =>
  (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
set_option hygiene false in
local notation "modulusP" => modularCharacter_standardParabolicPoints hG hi hν I rfl
  (RationalPointFamily.rootSet_subset i ν I)
set_option hygiene false in
local notation "weightSmooth" =>
  isSmoothFiniteTorusFunction_standardLeviPlancherelWeight hG hi hν I hζ π CM hCM mu hsq
    hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ
    hDReverse hneReverse hDReverseΩ hD hne hirr hreg

include hK0c hbasis hcover in
/-- The actual projected Levi compact and the ambient basis and Levi Cartan
cover give finite input derivative bounds for the original packet. -/
theorem standardLeviPacketCentralDerivativeEstimates_of_squareIntegrable : centralEstimates := by
  let := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
  let : CompactSpace (K : Subgroup (rationalPoints G)) := isCompact_iff_compactSpace.mp hKc
  let := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  let KM := rationalProjectedLeviCompact hG hi hν I (K := K)
  have hKMc := isCompact_rationalProjectedLeviCompact hG hi hν I hKc
  let : CompactSpace KM := isCompact_iff_compactSpace.mp hKMc
  have hKMo := isOpen_rationalProjectedLeviCompact hG hi hν I (K := K)
  have hMK := isIwasawaPair_rationalProjectedLeviCompact hG hi hν I hPK
  have hcoeff := hasXiBoundedCoefficients_standardLeviProjectedCompact hG hi hν I hKc hPK
    hK0c hbasis hcover π CM hCM mu hsq
  intro H hHK r
  refine exists_levelOrbitWavePacket_central_decay_of_coefficient_bound decomp closedU closedP K hKc
    factorization unimodular modulusP νM π normContinuous projectionContinuous coordinates
    CM hCM mu hsq rhoX W (leviRationalUnitaryCoordinates_hasLaurent hG hi hν I)
    (leviRationalUnitaryCoordinates hG hi hν I).continuous weightSmooth
    (rationalValuationCoordinatesHom G hG) (leviValuationRestrictionMatrix hG hi hν I)
    (fun k hk => rationalValuationCoordinatesHom_eq_one_of_mem_compact hG hKc hk)
    (fun u hu => rationalValuationCoordinatesHom_eq_one_of_mem_standardUnipotent hG hi hν I hu)
    (fun m z => leviRationalUnitaryCoordinates_symm_finiteTorusMonomial_apply hG hi hν I m z)
    (rationalXi hKc hPK) (fun v => ?_) (compactOpenCofinal_standardLevi I hKc) H hHK r
  obtain ⟨c, hc, hb⟩ := norm_twist_coefficientMap_le_xi_arbitraryCompact decomp closedU π.obj K hKc
    νM normContinuous closedP projectionContinuous
    (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK) unimodular modulusP π.property.2
    (isUnimodularModulus_standardUnipotentPoints hG hi hν I rfl)
    (rationalLeviData hG hi hν (RationalPointFamily.rootSet_subset i ν I) K.isOpen hKc) hPK
    KM hMK hKMo
    (standardLeviMinimalModulusOf_eq_one_sourceCompact hG hi hν
      (RationalPointFamily.rootSet_subset i ν I) hKMo hKMc)
    (fun p hp => rationalMinimalModulus_eq_one i ν K.isOpen hKc p hp)
    hcoeff v
  exact ⟨c, hc, fun y g => hb _ (norm_unitaryTorusParameter_apply νM coordinates y) g⟩

include hK0c hbasis hcover in
/-- Full-height estimates on Cartan cell points where all root pairings are bounded
by a fixed multiple of one plus the central coordinate norm. In particular, a
uniform bound on the root pairings suffices. -/
theorem exists_standardLeviPacket_height_derivative_bound_on_cartan_cells
    {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))
    (F0 : Finset (centralizerPoints i)) (T : ℝ) (hT : 0 ≤ T) :
    letI := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
    ∀ (H : OpenSubgroup (rationalPoints G)), H ≤ K → ∀ r : ℝ,
      ∃ t : Finset DerivativeIndex, ∃ c : ℝ≥0,
        ∀ (q : SectionLevel H) (y : cocharacterLattice S) (g : rationalPoints G),
          g ∈ rationalCartanCell i K0 F0 y →
          (∀ β : RationalPointFamily.SimpleRoot i ν,
            |(Langlands.Aubert.General.simpleRootPairing i ν β y : ℝ)| ≤
              T * (1 + ‖rationalValuationCoordinates G hG g‖)) →
          ‖packet (includeLevel H q) g‖ ≤
            (c : ℝ) * (t.sup (inputSeminorms H)) q * rationalXi hKc hPK g *
              (1 + rationalHeight (F := F) ρ g) ^ (-r) := by
  let := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
  intro H hHK r
  obtain ⟨A, hA, hheight⟩ := exists_rationalHeight_le_cartanCell_coordinates hG hi hν hK0c F0 ρ
  let D : ℝ := 1 + A * (1 + T)
  have hDgeOne : 1 ≤ D := le_add_of_nonneg_right (mul_nonneg hA (by linarith))
  have hDnonneg : 0 ≤ D := zero_le_one.trans hDgeOne
  have hcentral : centralEstimates :=
    standardLeviPacketCentralDerivativeEstimates_of_squareIntegrable hG hi hν I hζ s hs hindex π mu hsq
      hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ
      hDReverse hneReverse hDReverseΩ hD hne hirr hreg hKc hPK hK0c hbasis hcover
  obtain ⟨t, c, hb⟩ := hcentral H hHK (max r 0)
  let P : Seminorm ℂ (SectionLevel H) := c • t.sup (inputSeminorms H)
  have hP (q : SectionLevel H) : P q = (c : ℝ) * (t.sup (inputSeminorms H)) q := by
    simp [P, NNReal.smul_def]
  let d := Real.toNNReal (D ^ (max r 0))
  refine ⟨t, d * c, fun q y g hg hβ => ?_⟩
  have hnorm := norm_nonneg (rationalValuationCoordinates G hG g)
  have hcompare : 1 + rationalHeight (F := F) ρ g ≤
      D * (1 + ‖rationalValuationCoordinates G hG g‖) := by
    have h := hheight y _ (mul_nonneg hT (by linarith)) hβ g hg
    dsimp [D]
    nlinarith
  have he := norm_le_heightComparisonSeminorm (fun _ => P)
    (fun q g => packet (includeLevel H q) g) (rationalXi hKc hPK)
    (rationalHeight (F := F) ρ) (fun g => ‖rationalValuationCoordinates G hG g‖)
    hDgeOne r q g (rationalXi_nonneg hKc hPK g) (rationalHeight_nonneg ρ g) hnorm hcompare
    (by simpa only [hP] using hb q g)
  rw [heightComparisonSeminorm_apply _ hDnonneg, hP] at he
  simpa only [NNReal.coe_mul, d, Real.coe_toNNReal _ (Real.rpow_nonneg hDnonneg _), mul_assoc] using he

end Langlands.HarishChandraSchwartz
