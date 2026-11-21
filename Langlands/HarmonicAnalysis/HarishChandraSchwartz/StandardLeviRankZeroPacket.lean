import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RankZeroPacketStructure
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviPlancherelWavePacketChamberAssembly
import Langlands.GroupScheme.Rational.StandardParabolicEndpointsProof

/-! # Source-normalized standard-Levi synthesis in relative semisimple rank zero -/

noncomputable section

set_option maxRecDepth 10000
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
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x}

set_option hygiene false in
local notation "𝐋" => Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I)

local instance rankZeroSynthesisAffineHom : IsAffineHom 𝐋.X.hom :=
  leviScheme_isAffineHom i ν (RationalPointFamily.rootSet i ν I)
local instance rankZeroSynthesisAffine : IsAffine 𝐋.X.left :=
  isAffine_of_isAffineHom 𝐋.X.hom
local instance rankZeroSynthesisFiniteType : LocallyOfFiniteType 𝐋.X.hom :=
  leviScheme_locallyOfFiniteType i ν (RationalPointFamily.rootSet i ν I)
local instance rankZeroSynthesisTopology : TopologicalSpace (rationalPoints 𝐋) :=
  rationalPointTopology F 𝐋.X
local instance rankZeroSynthesisNonarchimedean : NonarchimedeanGroup (rationalPoints 𝐋) :=
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

variable {n : ℕ} [Nonempty (Fin n)] (ρ : MatrixRepresentation G (Fin n))

set_option hygiene false in
local notation "target" => StandardLeviPlancherelWavePacketSourceNormalizedStatement
  hG hi hν I hζ s hs hindex π mu hsq hRefl hCST Ks hKs hPKs hOppKs p qrev
  hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg hKc hPK ρ

/-- The original source-normalized joint conclusion at relative
semisimple rank zero. -/
def StandardLeviPlancherelWavePacketRankZeroStatement : Prop :=
  relativeRootRank i = 0 → target

set_option maxHeartbeats 1600000 in
/-- The central Fourier and height estimates give the exact rank-zero
source-normalized membership and continuity conclusions. -/
theorem standardLeviPlancherelWavePacketRankZero :
    StandardLeviPlancherelWavePacketRankZeroStatement hG hi hν I hζ s hs hindex π mu hsq
      hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ hDReverse
      hneReverse hDReverseΩ hD hne hirr hreg hKc hPK ρ := by
  intro hzero
  obtain ⟨hK0c, hbasis, hcover⟩ := RankZero.packetStructure_of_rankZero hG hi ν hν hzero
  have hsimple := simpleRelativeRoots_eq_empty_of_relativeRoots_eq_empty i ν
    (RankZero.relativeRoots_eq_empty_of_rankZero hG hi hzero)
  have hLevi := (standardParabolicEndpoints F G hG S i hi ν hν).2.2.2.1
  have hcoverAmbient : RationalPointFamily.FiniteCartanCovering F i ν (rationalCommonNormKernel G) := by
    obtain ⟨B, hB⟩ := hcover (simpleRelativeRoots i ν) Set.Subset.rfl
    refine ⟨B, fun g => ?_⟩
    have hg : g ∈ standardLeviPoints i ν (simpleRelativeRoots i ν) := by
      change g ∈ (standardLevi i ν (simpleRelativeRoots i ν)).carrier (Over.mk (𝟙 _))
      rw [hLevi]
      exact Subgroup.mem_top g
    obtain ⟨k₁, k₂, f, a, hk₁, hk₂, hf, ha, hfact⟩ := hB g hg
    exact ⟨k₁, k₂, f, a, hk₁.1, hk₂.1, hf, ha, hfact⟩
  let := hi.isSplitSubtorus.1.finite_realCocharacterSpace
  let b := Module.finBasis ℝ (RealTorusSpace.V S)
  let N := (normSeminorm ℝ (Fin (Module.finrank ℝ (RealTorusSpace.V S)) → ℝ)).comp
    b.equivFun.toLinearMap
  have hN (v : RealTorusSpace.V S) (hv : N v = 0) : v = 0 := by
    apply b.equivFun.injective
    rw [map_zero]
    exact norm_eq_zero.mp hv
  have hchamber := standardLeviPacketChamberDerivativeEstimates_of_properRegions
    hG hi hν I hζ s hs hindex π mu hsq hRefl hCST Ks hKs hPKs hOppKs p qrev
    hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg
    hKc hPK ρ hK0c hbasis (hcover ∅ (Set.empty_subset _))
    (hcover (RationalPointFamily.rootSet i ν I) (RationalPointFamily.rootSet_subset i ν I)) N hN
    (fun J hJ => False.elim ((not_lt_of_ge (Set.empty_subset _)) (hsimple ▸ hJ)))
  have hest := standardLeviPacketDerivativeEstimates_of_chamber hG hi hν I hζ s hs hindex π mu hsq
    hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ hDReverse
    hneReverse hDReverseΩ hD hne hirr hreg hKc hPK ρ hK0c hcoverAmbient hchamber
  exact standardLeviPlancherelWavePacketSourceNormalized_of_estimates
    hG hi hν I hζ s hs hindex π mu hsq hRefl hCST Ks hKs hPKs hOppKs p qrev
    hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg hKc hPK ρ hest

end Langlands.HarishChandraSchwartz
