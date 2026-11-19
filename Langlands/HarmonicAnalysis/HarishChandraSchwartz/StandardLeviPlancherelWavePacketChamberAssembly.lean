import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviPlancherelWavePacketCentralDerivative
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviPlancherelWavePacketCartanReduction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalLeviPacketRegions

/-! # Assembly of the original chamber estimates from proper-parabolic regions -/

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

local instance standardLeviPacketChamberAssemblyAffineHom : IsAffineHom 𝐋.X.hom :=
  leviScheme_isAffineHom i ν (RationalPointFamily.rootSet i ν I)
local instance standardLeviPacketChamberAssemblyAffine : IsAffine 𝐋.X.left :=
  isAffine_of_isAffineHom 𝐋.X.hom
local instance standardLeviPacketChamberAssemblyFiniteType : LocallyOfFiniteType 𝐋.X.hom :=
  leviScheme_locallyOfFiniteType i ν (RationalPointFamily.rootSet i ν I)
local instance standardLeviPacketChamberAssemblyTopology : TopologicalSpace (rationalPoints 𝐋) :=
  rationalPointTopology F 𝐋.X
local instance standardLeviPacketChamberAssemblyNonarchimedean : NonarchimedeanGroup (rationalPoints 𝐋) :=
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

variable {n : ℕ} [Nonempty (Fin n)] (ρ : MatrixRepresentation G (Fin n))

/-- The estimate still needed on intersections of the proper-Levi threshold
and positive-part regions, for the original source-normalized packet. -/
def StandardLeviPacketProperRegionDerivativeEstimates
    (N : Seminorm ℝ (RealTorusSpace.V S)) : Prop :=
  letI := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
  ∀ J : Finset (RationalPointFamily.SimpleRoot i ν),
    RationalPointFamily.rootSet i ν J ⊂ simpleRelativeRoots i ν →
    ∀ δ > 0, ∀ (H : OpenSubgroup (rationalPoints G)), H ≤ K → ∀ r : ℝ,
      ∃ t > (0 : ℝ), ∃ F0 : Finset DerivativeIndex, ∃ c : ℝ≥0,
        ∀ (q : SectionLevel H) (m : standardLeviPoints i ν ∅),
          m ∈ rationalConstantTermThresholdRegion hG hi hν (RationalPointFamily.rootSet i ν J) t →
          m ∈ rationalPositivePartRegion hG hi hν N (RationalPointFamily.rootSet i ν J) δ →
          ‖packet (includeLevel H q) m‖ ≤ (c : ℝ) * (F0.sup (inputSeminorms H)) q *
            (rationalXi hKc hPK m * (1 + rationalHeight (F := F) ρ m) ^ (-r))

set_option hygiene false in
local notation "properEstimates" => StandardLeviPacketProperRegionDerivativeEstimates hG hi hν I hζ
  s hs hindex π mu hsq hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ
  hDReverse hneReverse hDReverseΩ hD hne hirr hreg hKc hPK ρ
set_option hygiene false in
local notation "chamberEstimates" => StandardLeviPacketChamberDerivativeEstimates hG hi hν I hζ
  s hs hindex π mu hsq hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ
  hDReverse hneReverse hDReverseΩ hD hne hirr hreg hKc hPK ρ

/-- The proved central Fourier estimate and the proper-region bounds give the
entire closed-chamber derivative estimate for the original packet. -/
theorem standardLeviPacketChamberDerivativeEstimates_of_properRegions
    {K0 : Subgroup (rationalPoints G)} (hK0c : IsCompact (K0 : Set (rationalPoints G)))
    (hbasis : SimultaneousStandardBasisAt i ν K0)
    (hcover0 : StandardLeviCartanCovering F i ν ∅ K0)
    (hcover : StandardLeviCartanCovering F i ν (RationalPointFamily.rootSet i ν I) K0)
    (N : Seminorm ℝ (RealTorusSpace.V S)) (hN : ∀ v, N v = 0 → v = 0)
    (hproper : properEstimates N) : chamberEstimates := by
  classical
  let := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
  let : Fintype (RationalPointFamily.SimpleRoot i ν) :=
    (hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν).fintype
  let Proper := {J : Finset (RationalPointFamily.SimpleRoot i ν) //
    RationalPointFamily.rootSet i ν J ⊂ simpleRelativeRoots i ν}
  let : Fintype Proper := Fintype.ofFinite Proper
  obtain ⟨δ, hδ, hregions⟩ := exists_rationalMinimalLevi_height_or_packetRegions
    hG hi hν hK0c hcover0 N hN ρ
  intro H r
  choose threshold hthreshold support mult hbound using
    fun J : Proper => hproper J.val J.property δ hδ H.1 H.2 r
  let t : ℝ := 1 + ∑ J : Proper, |threshold J|
  have hthreshold_le (J : Proper) : threshold J ≤ t := (le_abs_self _).trans
    ((Finset.single_le_sum (fun J _ => abs_nonneg (threshold J)) (Finset.mem_univ J)).trans
      (le_add_of_nonneg_left zero_le_one))
  obtain ⟨D0, hD0, hsplit⟩ := hregions t
  have hD0nonneg : 0 ≤ D0 := zero_le_one.trans hD0
  have hcentral := standardLeviPacketCentralDerivativeEstimates_of_squareIntegrable
    hG hi hν I hζ s hs hindex π mu hsq hRefl hCST Ks hKs hPKs hOppKs p qrev
    hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg hKc hPK
    hK0c hbasis hcover
  obtain ⟨Fcentral, ccentral, hbcentral⟩ := hcentral H.1 H.2 (max r 0)
  let c0 := Real.toNNReal (D0 ^ (max r 0)) * ccentral
  let P0 : Seminorm ℂ (SectionLevel H.1) := ccentral • Fcentral.sup (inputSeminorms H.1)
  let Ftotal := Fcentral ∪ Finset.univ.biUnion support
  let Ctotal := c0 + ∑ J : Proper, mult J
  refine ⟨Ftotal, Ctotal, fun q g hg => ?_⟩
  obtain ⟨m, hm, rfl⟩ := hg
  let kernel := rationalXi hKc hPK (m : rationalPoints G) *
    (1 + rationalHeight (F := F) ρ (m : rationalPoints G)) ^ (-r)
  have hkernel : 0 ≤ kernel := mul_nonneg (rationalXi_nonneg hKc hPK _)
    (Real.rpow_nonneg (by linarith [rationalHeight_nonneg ρ (m : rationalPoints G)]) _)
  have enlarge (Fc : Finset DerivativeIndex) (hc : Fc ⊆ Ftotal) (c : ℝ≥0) (hcc : c ≤ Ctotal)
      (hb : ‖packet (includeLevel H.1 q) m‖ ≤ (c : ℝ) * (Fc.sup (inputSeminorms H.1)) q * kernel) :
      ‖packet (includeLevel H.1 q) m‖ ≤ (Ctotal : ℝ) * (Ftotal.sup (inputSeminorms H.1)) q * kernel := by
    have hs : Fc.sup (inputSeminorms H.1) ≤ Ftotal.sup (inputSeminorms H.1) := Finset.sup_mono hc
    exact hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul hcc (hs q) (apply_nonneg _ _) Ctotal.coe_nonneg) hkernel)
  change ‖packet (includeLevel H.1 q) m‖ ≤ (Ctotal : ℝ) * (Ftotal.sup (inputSeminorms H.1)) q * kernel
  rcases hsplit m hm with hheight | ⟨J, hJ, htJ, hpos⟩
  · apply enlarge Fcentral Finset.subset_union_left c0 (le_add_of_nonneg_right bot_le)
    have hP (q : SectionLevel H.1) : P0 q = (ccentral : ℝ) * (Fcentral.sup (inputSeminorms H.1)) q := by
      simp [P0, NNReal.smul_def]
    have h := norm_le_heightComparisonSeminorm (fun _ => P0)
      (fun q g => packet (includeLevel H.1 q) g) (rationalXi hKc hPK)
      (rationalHeight (F := F) ρ) (fun g => ‖rationalValuationCoordinates G hG g‖)
      hD0 r q (m : rationalPoints G) (rationalXi_nonneg hKc hPK _) (rationalHeight_nonneg ρ _)
      (norm_nonneg _) hheight (by simpa only [hP] using hbcentral q m)
    rw [heightComparisonSeminorm_apply _ hD0nonneg, hP] at h
    simpa only [kernel, c0, NNReal.coe_mul, Real.coe_toNNReal _ (Real.rpow_nonneg hD0nonneg _),
      mul_assoc] using h
  · let J' : Proper := ⟨J, hJ⟩
    have htJ' : m ∈ rationalConstantTermThresholdRegion hG hi hν
        (RationalPointFamily.rootSet i ν J) (threshold J') :=
      ⟨htJ.1, fun a ha => (hthreshold_le J').trans (htJ.2 a ha)⟩
    have hsub : support J' ⊆ Ftotal := fun e he => Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨J', Finset.mem_univ _, he⟩)
    have hmult : mult J' ≤ Ctotal :=
      (Finset.single_le_sum (fun J _ => (bot_le : 0 ≤ mult J)) (Finset.mem_univ J')).trans
        (le_add_of_nonneg_left bot_le)
    exact enlarge (support J') hsub (mult J') hmult (hbound J' q m htJ' hpos)

end Langlands.HarishChandraSchwartz
