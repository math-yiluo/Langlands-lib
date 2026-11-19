import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitSectionCompactChange
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitPacketCompactChange
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviPlancherelWavePacketChamberAssembly

/-! # Transfer of the actual proper-region estimates to the original compact picture -/

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

local instance standardLeviPacketCompactChangeAffineHom : IsAffineHom 𝐋.X.hom :=
  leviScheme_isAffineHom i ν (RationalPointFamily.rootSet i ν I)
local instance standardLeviPacketCompactChangeAffine : IsAffine 𝐋.X.left :=
  isAffine_of_isAffineHom 𝐋.X.hom
local instance standardLeviPacketCompactChangeFiniteType : LocallyOfFiniteType 𝐋.X.hom :=
  leviScheme_locallyOfFiniteType i ν (RationalPointFamily.rootSet i ν I)
local instance standardLeviPacketCompactChangeTopology : TopologicalSpace (rationalPoints 𝐋) :=
  rationalPointTopology F 𝐋.X
local instance standardLeviPacketCompactChangeNonarchimedean : NonarchimedeanGroup (rationalPoints 𝐋) :=
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

variable {L : OpenSubgroup (rationalPoints G)}
  (hLc : IsCompact (L : Set (rationalPoints G)))
  (hPL : IsIwasawaPair (standardParabolicPoints i ν ∅) (L : Subgroup (rationalPoints G)))

set_option hygiene false in
local notation "W" => standardLeviPlancherelWeight hG hi hν I hζ π CM hCM mu hsq hRefl hCST
  Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ
  hD hne hirr hreg
set_option hygiene false in
local notation "rhoX" => standardLeviUnitaryUnramifiedCharacterHaar I s hs hindex
set_option hygiene false in
local notation "omegaπ" => discreteSeriesClass CM hCM mu π hsq
set_option hygiene false in
local notation "packetAt[" hk ", " hw "]" => standardLeviPlancherelWavePacket hG hi hν I hζ π CM hCM mu hsq
  hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ hDReverse
  hneReverse hDReverseΩ hD hne hirr hreg hk hw rhoX

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
  (RationalPointFamily.rootSet_subset i ν I) decomp
set_option hygiene false in
local notation "factorization[" hk "]" =>
  factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hk)
set_option hygiene false in
local notation "coordinates" => (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv
set_option hygiene false in
local notation "SectionLevel[" A ", " hc ", " hp "]" => OrbitSectionLevel νM π coordinates decomp closedU A closedP
  hc normContinuous projectionContinuous factorization[hp]
set_option hygiene false in
local notation "includeLevel[" A ", " hc ", " hp "]" => OrbitSectionLevel.toSections νM π coordinates decomp closedU A
  closedP hc normContinuous projectionContinuous factorization[hp]
set_option hygiene false in
local notation "inputSeminorms[" A ", " hc ", " hp "]" => OrbitSectionLevel.seminormFamily νM π coordinates decomp closedU A
  closedP hc normContinuous projectionContinuous factorization[hp]

/-- The same actual standard-Levi section on the common open level in the new compact picture. -/
def standardLeviPacketChangeCompactLevel (H : OpenSubgroup (rationalPoints G)) :
    SectionLevel[K, hKc, hPK] H →ₗ[ℂ] SectionLevel[L, hLc, hPL] (H ⊓ L) :=
  orbitSectionLevelChangeCompact decomp closedU closedP K L hKc hLc factorization[hPK]
    factorization[hPL] νM π normContinuous projectionContinuous coordinates
    (leviRationalUnitaryCoordinates_hasLaurent hG hi hν I) H

set_option hygiene false in
local notation "changeLevel" => standardLeviPacketChangeCompactLevel hG hi hν I π hKc hPK hLc hPL

variable {n : ℕ} [Nonempty (Fin n)] (ρ : MatrixRepresentation G (Fin n))

set_option hygiene false in
local notation "properEstimates[" hc ", " hp "]" => StandardLeviPacketProperRegionDerivativeEstimates hG hi hν I hζ
  s hs hindex π mu hsq hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ
  hDReverse hneReverse hDReverseΩ hD hne hirr hreg hc hp ρ

/-- Establish the proper-region bounds with any compact open Iwasawa factor,
and transfer them to the exact normalization of the original packet. -/
theorem standardLeviPacketProperRegionDerivativeEstimates_of_compactChange
    (N : Seminorm ℝ (RealTorusSpace.V S)) (hproper : properEstimates[hLc, hPL] N) :
    properEstimates[hKc, hPK] N := by
  classical
  let := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
  obtain ⟨a, ha, hpacket⟩ := exists_pos_rationalInducedOrbitWavePacket_eq_mul_of_compact
    hG hi hν I hKc hLc hPK hPL π CM hCM mu hsq
  obtain ⟨b, hb⟩ := exists_rationalXi_le_mul L.isOpen hLc hPL K.isOpen hKc hPK
  have hb' (g : rationalPoints G) : rationalXi hLc hPL g ≤
      (Real.toNNReal b : ℝ) * rationalXi hKc hPK g :=
    (hb g).trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal b) (rationalXi_nonneg hKc hPK g))
  intro J hJ δ hδ H _ r
  obtain ⟨t, ht, support, d, hbound⟩ := hproper J hJ δ hδ (H ⊓ L) inf_le_right r
  obtain ⟨support', d', hlevel⟩ := exists_orbitSectionLevelChangeCompact_finsetSup_bound
    decomp closedU closedP K L hKc hLc factorization[hPK] factorization[hPL] νM π
    normContinuous projectionContinuous coordinates (leviRationalUnitaryCoordinates_hasLaurent hG hi hν I)
    H support
  let c : ℝ≥0 := ⟨a, ha.le⟩ * d * d' * Real.toNNReal b
  refine ⟨t, ht, support', c, fun q m hm hregion => ?_⟩
  let q' := changeLevel H q
  have hnorm : ‖packetAt[hKc, hPK] (includeLevel[K, hKc, hPK] H q) m‖ =
      a * ‖packetAt[hLc, hPL] (includeLevel[L, hLc, hPL] (H ⊓ L) q') m‖ := by
    have he := hpacket rhoX W (includeLevel[K, hKc, hPK] H q)
      (includeLevel[L, hLc, hPL] (H ⊓ L) q') rfl (m : rationalPoints G)
    calc
      _ = ‖(a : ℂ) * packetAt[hLc, hPL] (includeLevel[L, hLc, hPL] (H ⊓ L) q') m‖ :=
        congrArg norm he
      _ = _ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  let w := (1 + rationalHeight (F := F) ρ (m : rationalPoints G)) ^ (-r)
  have hw : 0 ≤ w := Real.rpow_nonneg (by linarith [rationalHeight_nonneg ρ (m : rationalPoints G)]) _
  let pL := (support.sup (inputSeminorms[L, hLc, hPL] (H ⊓ L))) q'
  let pK := (support'.sup (inputSeminorms[K, hKc, hPK] H)) q
  have hpK : 0 ≤ pK := apply_nonneg _ _
  rw [hnorm]
  calc
    _ ≤ a * ((d : ℝ) * pL * (rationalXi hLc hPL m * w)) :=
      mul_le_mul_of_nonneg_left (hbound q' m hm hregion) ha.le
    _ ≤ a * ((d : ℝ) * ((d' : ℝ) * pK) * (rationalXi hLc hPL m * w)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hlevel q) d.coe_nonneg)
        (mul_nonneg (rationalXi_nonneg hLc hPL m) hw)) ha.le
    _ ≤ a * ((d : ℝ) * ((d' : ℝ) * pK) * (((Real.toNNReal b : ℝ) * rationalXi hKc hPK m) * w)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hb' m) hw)
        (mul_nonneg d.coe_nonneg (mul_nonneg d'.coe_nonneg hpK))) ha.le
    _ = _ := by
      change _ = (a * (d : ℝ) * (d' : ℝ) * (Real.toNNReal b : ℝ)) * pK *
        (rationalXi hKc hPK m * w)
      ring

end Langlands.HarishChandraSchwartz
