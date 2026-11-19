import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviPlancherelWavePacketEstimates
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitSectionCartanReduction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalLeviHeight
import Langlands.Representation.Aubert.General.RationalCartanSupportReduction

/-! # The chamber suffices for the original source-normalized packet estimates -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal Pointwise
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Plancherel Langlands.Aubert.General
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

local instance standardLeviPacketCartanReductionAffineHom : IsAffineHom 𝐋.X.hom :=
  leviScheme_isAffineHom i ν (RationalPointFamily.rootSet i ν I)
local instance standardLeviPacketCartanReductionAffine : IsAffine 𝐋.X.left :=
  isAffine_of_isAffineHom 𝐋.X.hom
local instance standardLeviPacketCartanReductionFiniteType : LocallyOfFiniteType 𝐋.X.hom :=
  leviScheme_locallyOfFiniteType i ν (RationalPointFamily.rootSet i ν I)
local instance standardLeviPacketCartanReductionTopology : TopologicalSpace (rationalPoints 𝐋) :=
  rationalPointTopology F 𝐋.X
local instance standardLeviPacketCartanReductionNonarchimedean : NonarchimedeanGroup (rationalPoints 𝐋) :=
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
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))

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
local notation "sectionIdentity" => OrbitSectionSpace.toSections νM π coordinates decomp closedU K
  closedP hKc normContinuous projectionContinuous factorization
set_option hygiene false in
local notation "synthL" => standardLeviPlancherelWavePacketLinear hG hi hν I hζ s hs hindex π mu hsq
    hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ
    hDReverse hneReverse hDReverseΩ hD hne hirr hreg hKc hPK ∘ₗ sectionIdentity

set_option hygiene false in
local notation "chamber" => Subtype.val '' rationalMinimalClosedChamber hG hi hν

set_option hygiene false in
local notation "translateLevel" => orbitSectionLevelTranslate decomp closedU closedP K hKc factorization
  νM π normContinuous projectionContinuous coordinates (leviRationalUnitaryCoordinates_hasLaurent hG hi hν I)

/-- The chamber estimate uses the exact section, weight, orbit measures, Xi and
full matrix height of the original packet. -/
def StandardLeviPacketChamberDerivativeEstimates : Prop :=
  letI := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
  OrbitSectionChamberDerivativeEstimates decomp closedU closedP K hKc factorization
    νM π normContinuous projectionContinuous coordinates (rationalXi hKc hPK)
    (rationalHeight (F := F) ρ) chamber synthL

set_option hygiene false in
local notation "chamberEstimates" => StandardLeviPacketChamberDerivativeEstimates hG hi hν I hζ
  s hs hindex π mu hsq hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ
  hDReverse hneReverse hDReverseΩ hD hne hirr hreg hKc hPK ρ
set_option hygiene false in
local notation "allEstimates" => StandardLeviPacketDerivativeEstimates hG hi hν I hζ
  s hs hindex π mu hsq hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ
  hDReverse hneReverse hDReverseΩ hD hne hirr hreg hKc hPK ρ

/-- The finite Cartan cover gives a compact double cover of the image of the
actual minimal-Levi chamber. The finite centralizer factors stay in a compact
set of left translations. -/
theorem exists_compact_cover_rationalMinimalClosedChamber
    {K0 : Subgroup (rationalPoints G)} (hK0c : IsCompact (K0 : Set (rationalPoints G)))
    (hcover : RationalPointFamily.FiniteCartanCovering F i ν K0) :
    ∃ A : Set (rationalPoints G), IsCompact A ∧ ∀ g : rationalPoints G,
      ∃ a ∈ A, ∃ b ∈ K0, ∃ m ∈ chamber, g = a * m * b := by
  obtain ⟨F0, hcover⟩ := hcover
  let mult (x : rationalPoints G × centralizerPoints i) : rationalPoints G := x.1 * x.2.val
  let A := mult '' ((K0 : Set (rationalPoints G)) ×ˢ (F0 : Set (centralizerPoints i)))
  have hA : IsCompact A := (hK0c.prod F0.finite_toSet.isCompact).image
    (continuous_fst.mul (continuous_subtype_val.comp continuous_snd))
  refine ⟨A, hA, fun g => ?_⟩
  obtain ⟨k₁, k₂, f, a, hk₁, hk₂, hf, ha, hg⟩ := hcover g
  obtain ⟨y, rfl, hy⟩ := exists_cocharacter_of_mem_CAplus i ν ha
  let m := minimalLeviUniformizer (i := i) (ν := ν) y
  have hm : m ∈ rationalMinimalClosedChamber hG hi hν := by
    intro β hβ
    rw [rationalMinimalH0_minimalLeviUniformizer, RealTorusSpace.eval_tmul, one_mul]
    exact_mod_cast hy ⟨β, hβ⟩
  refine ⟨k₁ * f.val, ⟨(k₁, f), ⟨hk₁, hf⟩, rfl⟩, k₂, hk₂, m.val, ⟨m, hm, rfl⟩, ?_⟩
  rw [coe_minimalLeviUniformizer]
  exact hg

/-- Translating an original level section translates the original packet. -/
theorem standardLeviPlancherelWavePacket_translateLevel :
    letI := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
    ∀ (H : OpenSubgroup (rationalPoints G)) (x : rationalPoints G × rationalPoints G)
      (q : SectionLevel H) (g : rationalPoints G),
      packet (includeLevel (orbitSectionTranslatedLevel K H x) (translateLevel H x q)) g =
        packet (includeLevel H q) (x.2⁻¹ * g * x.1) := by
  let := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
  let := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  exact inducedOrbitWavePacket_translateLevel decomp closedU closedP K hKc factorization
    νM π normContinuous projectionContinuous coordinates (leviRationalUnitaryCoordinates_hasLaurent hG hi hν I)
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl
      (RationalPointFamily.rootSet_subset i ν I)) CM hCM mu hsq rhoX W

/-- Derivative estimates on the closed minimal-Levi chamber extend to the
whole group for the original source-normalized packet. -/
theorem standardLeviPacketDerivativeEstimates_of_chamber
    {K0 : Subgroup (rationalPoints G)} (hK0c : IsCompact (K0 : Set (rationalPoints G)))
    (hcover : RationalPointFamily.FiniteCartanCovering F i ν K0)
    (hchamber : chamberEstimates) : allEstimates := by
  let := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
  let := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  let : CompactSpace (K : Subgroup (rationalPoints G)) := isCompact_iff_compactSpace.mp hKc
  obtain ⟨A, hA, hAC⟩ := exists_compact_cover_rationalMinimalClosedChamber hG hi hν hK0c hcover
  let D0 : OpenSubgroup (rationalPoints G) := K ⊓
    ⟨rationalHeightSubgroup (F := F) ρ, isOpen_rationalHeightSubgroup ρ⟩
  let he := leviRationalUnitaryCoordinates_hasLaurent hG hi hν I
  have hXi : UniformTranslationBound (rationalXi hKc hPK) :=
    xi_uniformTranslationBound (fun p hp => rationalMinimalModulus_eq_one i ν K.isOpen hKc p hp) K.isOpen
  refine orbitSectionSchwartzEstimates_of_compact_chamber decomp closedU closedP K hKc factorization
    νM π normContinuous projectionContinuous coordinates he (rationalXi hKc hPK)
    (rationalHeight (F := F) ρ) (rationalXi_pos K.isOpen hKc hPK) (rationalHeight_nonneg ρ)
    (rationalHeight_inv ρ) (rationalHeight_mul_le ρ) hXi D0
    (fun k hk l hl g => rationalXi_mul_mul K.isOpen hKc hPK hk.1 hl.1 g)
    (fun k hk l hl g => rationalHeight_mul_mul ρ hk.2 hl.2 g)
    hA hK0c hAC synthL ?_ ?_ hchamber
  · exact standardLeviPlancherelWavePacket_biInvariant_of_level hG hi hν I hζ s hs hindex π mu hsq
      hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ hDReverse hneReverse
      hDReverseΩ hD hne hirr hreg hKc hPK
  · exact standardLeviPlancherelWavePacket_translateLevel hG hi hν I hζ s hs hindex π mu hsq
      hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ hDReverse hneReverse
      hDReverseΩ hD hne hirr hreg hKc hPK

end Langlands.HarishChandraSchwartz
