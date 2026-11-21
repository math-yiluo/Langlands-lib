import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviLowerPacket
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakPacketLowerEstimates

/-! # Lower packet estimates from the source-normalized target at a lower Levi -/

noncomputable section

set_option maxRecDepth 10000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.Induction
open Langlands.HarmonicAnalysis.TorusFourier

namespace Langlands.HarishChandraSchwartz.LowerPacket

section Lower

open Langlands.Plancherel.DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar
open RationalPointFamily WeakExpansion LowerChamber LowerSplitCenter

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

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

attribute [local instance] lowerPacketLeviAffineHom lowerPacketLeviFiniteType

local instance lowerPacketAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance lowerPacketLeviAffine (J : Set (characterLattice T)) :
    IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom

variable (hi : IsMaximalSplitTorus i) (I' : Finset (SimpleRoot i ν))
  (ζ : cocharacterLattice T) (n : normalizerPoints i)
  (hG : IsConnectedReductive G) (hν : IsGenericCocharacter i ν)

set_option hygiene false in
local notation "M'" => lowerAmbient i ν (rootSet i ν I')
set_option hygiene false in
local notation "iL" => Standard.leviTorusHom i ν (rootSet i ν I')
set_option hygiene false in
local notation "c" => lowerChamber hi I' ζ n
set_option hygiene false in
local notation "hM'" => lowerAmbient_isConnectedReductive hG hi hν I'
set_option hygiene false in
local notation "hiL" => lowerTorus_isMaximalSplitTorus hi I'
set_option hygiene false in
local notation "χs" => lowerCocharacter i ν (rootSet i ν I') ζ n
set_option hygiene false in
local notation "e₀" => lowerChamberLeviHomeomorph hi I' ζ n hG hν
set_option hygiene false in
local notation "e₁" => lowerChamberLeviEquiv hi I' ζ n hG hν
set_option hygiene false in
local notation "Φ₂" => standardLeviParameterIso hM' hiL (c).isGeneric (c).labels (c).isStandard
set_option hygiene false in
local notation "𝐋'" => Standard.leviScheme iL (c).chamber (rootSet iL (c).chamber (c).labels)
-- The standard Levi `M_{J''}(F)` of `M'` for the chamber of `sζ`, as in the target.
set_option hygiene false in
local notation "𝐌'" => {x : rationalPoints M' //
  @Membership.mem (rationalPoints M') (Subgroup (rationalPoints M')) _
    (standardLeviPoints iL (c).chamber (rootSet iL (c).chamber (c).labels)) x}


variable (I : Finset (SimpleRoot i ν)) (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))

set_option hygiene false in
local notation "𝐋" => Standard.leviScheme i ν (rootSet i ν I)
set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}

variable {A : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine A.X.left] (s : A.toGrp ⟶ 𝐋)

set_option hygiene false in
local notation "CM" => rationalLeviSplitCenter I s
set_option hygiene false in
local notation "CM'" => rationalLeviSplitCenter (c).labels (lowerSplit hi I' ζ n hG hν I hζ hn s)
set_option hygiene false in
local notation "sC" => lowerCentral hG hi hν I I' hζ n hn CM

variable [(CM).Normal] [(CM').Normal]
  [MeasurableSpace (𝐌 ⧸ CM)] [BorelSpace (𝐌 ⧸ CM)]
  (mu : Measure (𝐌 ⧸ CM)) [mu.IsHaarMeasure]
  [MeasurableSpace (𝐌' ⧸ CM')] [BorelSpace (𝐌' ⧸ CM')]
  (hs : IsSplitComponent s)

set_option hygiene false in
local notation "hCM" => rationalLeviSplitCenter_le_center I s hs
set_option hygiene false in
local notation "hCM'" => rationalLeviSplitCenter_le_center (c).labels
  (lowerSplit hi I' ζ n hG hν I hζ hn s) (isSplitComponent_lowerSplit hi I' ζ n hG hν I hζ hn s hs)
set_option hygiene false in
local notation "hsC" => lowerCentral_le_center hG hi hν I I' hζ n hn CM hCM
set_option hygiene false in
local notation "mu'" => lowerChamberQuotientMeasure hi I' ζ n hG hν I hζ hn s mu

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (hsq : IsSquareIntegrableModCentralSubgroup CM hCM π.obj.representation mu)
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})

set_option hygiene false in
local notation "π'" => lowerChamberRepresentation hi I' ζ n hG hν I hζ hn π
set_option hygiene false in
local notation "hsq'" => lowerChamberRepresentation_isSquareIntegrable hi I' ζ n hG hν I hζ hn s
  mu hs π hsq
set_option hygiene false in
local notation "sμ" => lowerMeasure hG hi hν I I' hζ n hn CM mu
set_option hygiene false in
local notation "sω" => discreteSeriesClass (sC) hsC (sμ)
  (lowerRepresentation hG hi hν I I' hζ n hn π)
  (lowerRepresentation_isSquareIntegrable hG hi hν I I' hζ n hn CM hCM mu π hsq)

-- The Plancherel weight of the source-normalized target at `M'`, with the data of a package.
set_option hygiene false in
local notation "W'[" P "]" => standardLeviPlancherelWeight hM' hiL (c).isGeneric (c).labels
  (c).isStandard π' CM' hCM' mu' hsq' hRefl hCST (P).K (P).hK (P).hPK (P).hOppK (P).p (P).q
  (P).hDForward (P).hneForward (P).hDForwardΩ (P).hDReverse (P).hneReverse (P).hDReverseΩ
  (P).hD (P).hne (P).hirr (P).hreg
set_option hygiene false in
local notation "P'" => lowerChamberPackage hi I' ζ n hG hν I hζ hn π hRefl hCST P

set_option hygiene false in
local notation "ω'" => discreteSeriesClass CM' hCM' mu' π' hsq'


/-! #### Lower packet estimates from the target at `M'` -/

set_option hygiene false in
local notation "KL" P => lowerK hG hi hν I I' hζ n hn hRefl hCST π P
set_option hygiene false in
local notation "KcL" P => lowerK_isCompact hG hi hν I I' hζ n hn hRefl hCST π P
set_option hygiene false in
local notation "PKL" P => lowerPackage_iwasawa hG hi hν I I' hζ n hn hRefl hCST π P
set_option hygiene false in
local notation "πL" => lowerRepresentation hG hi hν I I' hζ n hn π
set_option hygiene false in
local notation "sqL" =>
  lowerRepresentation_isSquareIntegrable hG hi hν I I' hζ n hn CM hCM mu π hsq
set_option hygiene false in
local notation "ρL" => lowerCharacterMeasure hG hi hν I I' hζ n hn
  (standardLeviUnitaryUnramifiedCharacterHaar I s hs hindex)
set_option hygiene false in
local notation "finiteUpper" => finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu
  (discreteSeriesClass CM hCM mu π hsq)
set_option hygiene false in
local notation "finiteLower" => finite_lowerStabilizer hG hi hν I I' hζ n hn CM hCM mu π hsq

set_option hygiene false in
local notation "LowerLevel[" P "," H "]" =>
  OrbitSectionLevel (leviNormCharacters χs) πL
    (DynamicInducedOrbit.leviUnitaryCoordinates (H := M') hM' χs).toMulEquiv
    (decomposition χs) (radical_isClosed χs) (KL P) (parabolic_isClosed χs) (KcL P)
    (DynamicInducedOrbit.leviNormCharacters_continuous χs) (projection_continuous χs) (PKL P) H
set_option hygiene false in
local notation "lowerInclude[" P "," H "]" =>
  OrbitSectionLevel.toSections (G := RationalPoint F (M').X) (leviNormCharacters χs) πL
    (DynamicInducedOrbit.leviUnitaryCoordinates (H := M') hM' χs).toMulEquiv
    (decomposition χs) (radical_isClosed χs) (KL P) (parabolic_isClosed χs) (KcL P)
    (DynamicInducedOrbit.leviNormCharacters_continuous χs) (projection_continuous χs) (PKL P) H
set_option hygiene false in
local notation "lowerSeminorm[" P "," H "]" =>
  OrbitSectionLevel.seminormFamily (leviNormCharacters χs) πL
    (DynamicInducedOrbit.leviUnitaryCoordinates (H := M') hM' χs).toMulEquiv
    (decomposition χs) (radical_isClosed χs) (KL P) (parabolic_isClosed χs) (KcL P)
    (DynamicInducedOrbit.leviNormCharacters_continuous χs) (projection_continuous χs) (PKL P) H
set_option hygiene false in
local notation "LowerDerivativeIndex[" P "]" =>
  List (Fin (rationalImageRank (parameterScheme χs))) ×
    Module.Dual ℂ (ProductInducedCompactPicture (decomposition χs) (KL P) (πL).obj)

set_option maxHeartbeats 2500000 in
private def lowerLevelPacket [(rationalPoints.map s).range.Normal]
    (hindex : (RenardCartan.splitValuationImage s).FiniteIndex)
    (P : LowerDensityPackage hG hi hν I I' hζ n hn π hRefl hCST)
    (H : OpenSubgroup (RationalPoint F (M').X)) (q : LowerLevel[P, H])
    (x : RationalPoint F (M').X) : ℂ :=
  letI := finiteUpper
  letI := finiteLower
  DynamicInducedOrbit.inducedOrbitWavePacket (H := M') hM' χs (KcL P) (PKL P) πL (sC) hsC (sμ) sqL
    (ρL) (lowerPlancherelWeight hG hi hν I I' hζ n hn CM hCM mu π hsq hRefl hCST P)
    (lowerInclude[P, H] q) x

set_option hygiene false in
local notation "lowerPacket[" P "," H "]" =>
  lowerLevelPacket hi I' ζ n hG hν I hζ hn s mu hs π hsq hRefl hCST hindex P H

set_option maxHeartbeats 2500000 in
/-- The exact published packet continuity target specialized to the standard chamber of the
lower cocharacter, with the transported split component, representation, measure and density. -/
abbrev LowerChamberPacketContinuity
    (P : LowerDensityPackage hG hi hν I I' hζ n hn π hRefl hCST)
    (hPK' : IsIwasawaPair (standardParabolicPoints iL (c).chamber ∅)
      (lowerK hG hi hν I I' hζ n hn hRefl hCST π P : Subgroup (rationalPoints M')))
    {N : ℕ} [Nonempty (Fin N)] (ρ' : MatrixRepresentation M' (Fin N)) : Prop :=
  haveI := lowerSplit_range_normal hi I' ζ n hG hν I hζ hn s hs
  StandardLeviPlancherelWavePacketContinuityStatement hM' hiL (c).isGeneric (c).labels
    (c).isStandard (lowerSplit hi I' ζ n hG hν I hζ hn s)
    (isSplitComponent_lowerSplit hi I' ζ n hG hν I hζ hn s hs)
    (finiteIndex_lowerSplit hi I' ζ n hG hν I hζ hn s hs) π' mu' hsq' hRefl hCST
    (P').K (P').hK (P').hPK (P').hOppK (P').p (P').q (P').hDForward (P').hneForward
    (P').hDForwardΩ (P').hDReverse (P').hneReverse (P').hDReverseΩ (P').hD (P').hne
    (P').hirr (P').hreg (lowerK_isCompact hG hi hν I I' hζ n hn hRefl hCST π P) hPK' ρ'

set_option maxHeartbeats 12000000 in
/-- **Lower packet estimates from continuity at `M'`.** Let `P` be a supplied lower density
package whose compact open subgroup `K' = lowerK P` of `M'(F)` forms an Iwasawa pair with the
minimal standard parabolic for the chamber of `sζ`, and let `ρ'` be a matrix representation of
`M'`. If the source-normalized continuity target holds at `M'` for the transported data, then
for every open `H ≤ K'` and real `r` the lower packets of sections of coefficient level `H`
satisfy `|E(q)(x)| ≤ b · (sup_{i ∈ t} p_i)(q) · Ξ^{M'}(x) (1 + σ'(x))^{-r}` at every `x ∈ M'(F)`. -/
theorem exists_lowerPacket_bound [(rationalPoints.map s).range.Normal]
    (hindex : (RenardCartan.splitValuationImage s).FiniteIndex)
    (P : LowerDensityPackage hG hi hν I I' hζ n hn π hRefl hCST)
    (hPK' : IsIwasawaPair (standardParabolicPoints iL (c).chamber ∅)
      (lowerK hG hi hν I I' hζ n hn hRefl hCST π P : Subgroup (rationalPoints M')))
    {N : ℕ} [Nonempty (Fin N)] (ρ' : MatrixRepresentation M' (Fin N))
    (hIH : LowerChamberPacketContinuity hi I' ζ n hG hν I hζ hn s mu hs π hsq hRefl hCST P hPK' ρ')
    (H : OpenSubgroup (RationalPoint F (M').X))
    (hH : H ≤ lowerK hG hi hν I I' hζ n hn hRefl hCST π P) (r : ℝ) :
    LevelPacketBound lowerSeminorm[P, H] lowerPacket[P, H]
      (rationalXi (KcL P) hPK') (rationalHeight (F := F) ρ') r := by
  have := finiteUpper
  have := finiteLower
  have := lowerSplit_range_normal hi I' ζ n hG hν I hζ hn s hs
  have := finite_lowerChamberStabilizer hi I' ζ n hG hν I hζ hn s mu hs π hsq
  have := locallyCompactSpace_standardParabolicPoints_rootSet hM' hiL (c).isGeneric (c).labels
  let : MeasurableSpace (RationalPoint F (M').X) := borel _
  have : BorelSpace (RationalPoint F (M').X) := ⟨rfl⟩
  have : LocallyCompactSpace (parabolic χs) := (parabolic_isClosed χs).locallyCompactSpace
  have : CompactSpace ((KL P : Subgroup (RationalPoint F (M').X)).subgroupOf (levi χs)) :=
    isCompact_iff_compactSpace.mp
      ((DynamicOppositeStandardIntertwining.levi_isClosed χs).isClosedEmbedding_subtypeVal.isCompact_preimage
        (KcL P))
  obtain ⟨synth, hsynth⟩ := hIH
  -- Fix the ambient topology before instantiating the dependent section types.
  let transport := @exists_packet_bound_of_subgroupChange
    (RationalPoint F (M').X) inferInstance (dynamicOppositeCanonicalScalarTopologicalSpace (G := M'))
  have d := transport (P := parabolic χs) (M := levi χs) (U := radical χs)
    (I := rationalCharacters (parameterScheme χs)) (J := Fin (rationalImageRank (parameterScheme χs)))
    («P'» := standardParabolicPoints iL (c).chamber (rootSet iL (c).chamber (c).labels))
    («M'» := standardLeviPoints iL (c).chamber (rootSet iL (c).chamber (c).labels))
    (U' := standardUnipotentPoints iL (c).chamber (rootSet iL (c).chamber (c).labels))
    (decomposition χs) (radical_isClosed χs) (parabolic_isClosed χs)
    (lowerK hG hi hν I I' hζ n hn hRefl hCST π P)
    (lowerK_isCompact hG hi hν I I' hζ n hn hRefl hCST π P)
    (lowerPackage_iwasawa hG hi hν I I' hζ n hn hRefl hCST π P)
    (fun g => rationalReductiveUnimodularity F M' hM' standardCocharacter g)
    (DynamicInducedOrbit.parabolic_modularCharacter_eq hM' χs)
    (lowerRepresentation hG hi hν I I' hζ n hn π) (projection_continuous χs)
    (leviNormCharacters χs) (DynamicInducedOrbit.leviNormCharacters_continuous χs)
    (DynamicInducedOrbit.leviUnitaryCoordinates (H := M') hM' χs).toMulEquiv
  have decomp' := isSemidirectDecomposition_standard hM' hiL (c).isGeneric
    (rootSet_subset iL (c).chamber (c).labels)
  have st₁ := d decomp'
    (isClosed_standardUnipotentPoints iL (c).chamber (rootSet iL (c).chamber (c).labels))
    (isClosed_standardParabolicPoints_rootSet hM' hiL (c).isGeneric (c).labels)
  have fact' := factorization_subtype
    (exists_standardParabolicPoints_rootSet_mul hM' hiL (c).isGeneric (c).labels hPK')
  have mod' := modularCharacter_standardParabolicPoints hM' hiL (c).isGeneric (c).labels rfl
    (rootSet_subset iL (c).chamber (c).labels)
  have proj' := continuous_projection_standard hM' hiL (c).isGeneric
    (rootSet_subset iL (c).chamber (c).labels) decomp'
  have st₂ := @st₁ fact' mod' proj'
  let norm' := leviRationalNormCharacters iL (c).chamber (c).labels
  have cont' : ∀ j, Continuous (norm' j) :=
    continuous_leviRationalNormCharacters iL (c).chamber (c).labels
  let coord' := (leviRationalUnitaryCoordinates (G := M') hM' hiL (c).isGeneric (c).labels).toMulEquiv
  let iso' := e₁
  have st := st₂ (I' := rationalCharacters 𝐋') (J' := Fin (rationalImageRank 𝐋'))
    norm' cont' coord' iso'
  have cx := st (sC) hsC (sμ)
    (lowerRepresentation_isSquareIntegrable hG hi hν I I' hζ n hn CM hCM mu π hsq)
    CM' hCM' mu' (map_lowerSplitCenter hi I' ζ n hG hν I hζ hn s)
    (lowerChamberQuotientMeasure_map hi I' ζ n hG hν I hζ hn s mu) π' hsq'
  let rhoDyn := ρL
  let rhoStd := standardLeviUnitaryUnramifiedCharacterHaar (c).labels (lowerSplit hi I' ζ n hG hν I hζ hn s)
      (isSplitComponent_lowerSplit hi I' ζ n hG hν I hζ hn s hs)
      (finiteIndex_lowerSplit hi I' ζ n hG hν I hζ hn s hs)
  let w := lowerPlancherelWeight hG hi hν I I' hζ n hn CM hCM mu π hsq hRefl hCST P
  let w' := W'[P']
  let τ := lowerChamberOrbitTransport hi I' ζ n hG hν I hζ hn s mu hs π hsq
  have cx' := cx rhoDyn rhoStd w w' τ
  have hτ := orbitTransport_val (e₁) (lowerChamberCharacterTransport hi I' ζ n hG hν I hζ hn)
    (lowerChamberCharacterTransport_apply hi I' ζ n hG hν I hζ hn) (sC) hsC CM' hCM'
    (map_lowerSplitCenter hi I' ζ n hG hν I hζ hn s) (sμ) mu'
    (lowerChamberQuotientMeasure_map hi I' ζ n hG hν I hζ hn s mu) (sω) (ω')
    (pullback_lowerClass hi I' ζ n hG hν I hζ hn s mu hs π hsq)
  have hτmu := map_lowerOrbitMeasure hi I' ζ n hG hν I hζ hn s mu hs π hsq hindex
  have hτw := standardLeviPlancherelWeight_lowerChamberOrbitTransport hi I' ζ n hG hν I hζ hn s mu hs π
      hsq hRefl hCST P
  have cx'' := cx' hτ hτmu hτw
  have hpar := (standardLeviPlancherelParabolic_eq hM' hiL (c).isGeneric (c).labels (c).isStandard).symm
  have hrad := congrArg (fun P => P.carrier (Over.mk (𝟙 _)))
    (Jacquet.standardLevi_eq_dynamic hM' hiL (c).isGeneric (c).isStandard).2
  have hkern := mem_commonNormKernel_lowerChamberLeviEquiv hi I' ζ n hG hν
  have hcoord := hasEvaluationUnitaryCoordinates_levi hM' χs
  have hlas := leviRationalUnitaryCoordinates_hasLaurent hM' hiL (c).isGeneric (c).labels
  have hident : ∀ x : 𝐌', ((e₁) x : rationalPoints M') = x := fun _ => rfl
  have hrep : π' = IrreducibleAdmissibleRep.pullback (e₁) (πL) := rfl
  have wt₀ := cx'' hident hpar hrad
  have wt₁ := @wt₀ hrep
  have wt₂ := @wt₁ hkern
  have wt₃ := @wt₂ hcoord
  have wt := @wt₃ hlas
  have wt' := wt
    (Ξ := rationalXi (KcL P) hPK') (σ := rationalHeight (F := F) ρ')
    (rationalXi_pos (KL P).isOpen (KcL P) hPK')
    (rationalHeight_nonneg ρ')
  have wtSynth := wt' synth
  have wtAgreement := wtSynth (fun q g => by
    refine (hsynth q g).trans ?_
    unfold inducedOrbitWavePacket
    dsimp only [rationalInducedOrbitCoefficientMap, norm', coord', rhoStd, w'])
  have hb := wtAgreement H hH r
  delta lowerLevelPacket DynamicInducedOrbit.inducedOrbitWavePacket
  dsimp only [rhoDyn, w] at hb ⊢
  simp only [OrbitSectionLevel.toSections] at hb ⊢
  with_unfolding_all exact hb

/-! #### The lower bounds in the weak constant-term expansion -/

private theorem rationalXi_eq_of_subgroup_eq {K₁ K₂ : Subgroup (rationalPoints G)}
    (h : K₁ = K₂) (hK₁ : IsCompact (K₁ : Set (rationalPoints G)))
    (hK₂ : IsCompact (K₂ : Set (rationalPoints G)))
    (hp₁ : IsIwasawaPair (standardParabolicPoints i ν ∅) K₁)
    (hp₂ : IsIwasawaPair (standardParabolicPoints i ν ∅) K₂) (x : rationalPoints G) :
    rationalXi hK₁ hp₁ x = rationalXi hK₂ hp₂ x := by
  subst K₂
  rfl

set_option hygiene false in
local notation "Index" => WeylIndex i ν (rootSet i ν I) (rootSet i ν I')
set_option hygiene false in
local notation "cutLevi" => standardLeviPoints i ν (rootSet i ν I')
set_option hygiene false in
local notation "Kₛ[" w "]" => lowerK hG hi hν I I' hζ (R.normalizer w) (R.levi_le w)
  hRefl hCST π (PM w)
set_option hygiene false in
local notation "cₛ[" w "]" => lowerChamber hi I' ζ (R.normalizer w)
set_option hygiene false in
local notation "νₛ[" w "]" => (cₛ[w]).chamber
set_option hygiene false in
local notation "Qₛ[" w "]" =>
  (standardLeviPoints iL νₛ[w] (rootSet iL νₛ[w] (cₛ[w]).labels)) ⧸
    rationalLeviSplitCenter (cₛ[w]).labels (lowerSplit hi I' ζ (R.normalizer w) hG hν I hζ (R.levi_le w) s)
set_option hygiene false in
local notation "ρM" => ρ.restrict (Standard.leviHom i ν (rootSet i ν I'))

set_option maxHeartbeats 8000000 in
/-- In the source compact normalization, the lower-Levi continuity hypotheses give the
chamber bounds for every Weyl summand of the actual weak constant-term expansion. The height
used at `M'` comes from restricting the given matrix representation of `G`. -/
theorem lowerDynamicPacketChamberEstimates_of_continuity [(rationalPoints.map s).range.Normal]
    (hindex : (RenardCartan.splitValuationImage s).FiniteIndex)
    {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
    (hMK : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf cutLevi)
      (K.toSubgroup.subgroupOf cutLevi))
    (PG : DynamicInducedOrbit.DensityPackage i ζ hRefl hCST hG
      (SmoothRep.pullback (standardLeviDynamicHomeomorph hG hi hν I hζ) π.obj))
    (R : Representatives i ν (rootSet i ν I) (rootSet i ν I'))
    (PM : ∀ w : Index, LowerDensityPackage hG hi hν I I' hζ (R.normalizer w) (R.levi_le w)
      π hRefl hCST)
    (hN : SourceCompactNormalization hG hi hν I I' hζ (K := K) π hRefl hCST PG R PM)
    {D : ℕ} [Nonempty (Fin D)] (ρ : MatrixRepresentation G (Fin D))
    (hIH : ∀ (w : Index) (hPK' : IsIwasawaPair (standardParabolicPoints iL νₛ[w] ∅)
      (Kₛ[w] : Subgroup (rationalPoints M'))),
      haveI := lowerSplitCenter_normal hi I' ζ (R.normalizer w) hG hν I hζ (R.levi_le w) s hs
      letI : MeasurableSpace Qₛ[w] := borel _
      haveI : BorelSpace Qₛ[w] := ⟨rfl⟩
      LowerChamberPacketContinuity hi I' ζ (R.normalizer w) hG hν I hζ (R.levi_le w)
        s mu hs π hsq hRefl hCST (PM w) hPK' ρM) :
    LowerDynamicPacketChamberEstimates hG hi hν I I' hζ hKc s hs hindex π mu hsq hRefl hCST
      R PM hMK ρ := by
  intro w H hH r
  have hKnorm : (Kₛ[w] : Subgroup (rationalPoints M')) =
      leviSchemeCompact K.toSubgroup i ν (rootSet i ν I') := (hN w).lower
  have hPKc := isIwasawaPair_lowerCompact hi I' ζ (R.normalizer w) hG hν hMK
  have hPK' : IsIwasawaPair (standardParabolicPoints iL νₛ[w] ∅)
      (Kₛ[w] : Subgroup (rationalPoints M')) := hKnorm.symm ▸ hPKc
  have := lowerSplitCenter_normal hi I' ζ (R.normalizer w) hG hν I hζ (R.levi_le w) s hs
  let : MeasurableSpace Qₛ[w] := borel _
  have : BorelSpace Qₛ[w] := ⟨rfl⟩
  have hb := exists_lowerPacket_bound hi I' ζ (R.normalizer w) hG hν I hζ (R.levi_le w)
    s mu hs π hsq hRefl hCST hindex (PM w) hPK' ρM (hIH w hPK') H hH r
  obtain ⟨t, b, h⟩ := hb
  refine ⟨t, b, fun q m _ => ?_⟩
  let j := leviRationalPointHomeomorph i ν I'
  let inc := minimalLeviInclusion hG hi hν (rootSet i ν I')
  let x : rationalPoints M' := j.symm (inc m)
  have hj : j x = inc m := j.apply_symm_apply _
  have he : leviSchemePointsEquiv i ν (rootSet i ν I') x = inc m := by
    refine Eq.trans (Subtype.ext ?_ : leviSchemePointsEquiv i ν (rootSet i ν I') x = j x) hj
    exact (leviSchemePointsEquiv_coe i ν (rootSet i ν I') x).trans
      (leviRationalPointHomeomorph_apply_coe i ν I' x).symm
  have hXi : rationalXi (lowerK_isCompact hG hi hν I I' hζ (R.normalizer w) (R.levi_le w)
      hRefl hCST π (PM w)) hPK' x = rationalLeviXi hKc hMK (inc m) := by
    calc
      _ = rationalXi (isCompact_leviSchemeCompact hKc) hPKc x :=
        rationalXi_eq_of_subgroup_eq hKnorm _ _ hPK' hPKc x
      _ = _ := (rationalXi_lowerCompact hi I' ζ (R.normalizer w) hG hν K.isOpen hKc hMK x).trans
        (congrArg (rationalLeviXi hKc hMK) he)
  have hHeight : rationalHeight (F := F) ρM x = rationalHeight (F := F) ρ (m : rationalPoints G) := by
    refine (rationalHeight_restrict_leviHom ρ x).trans (congrArg (rationalHeight (F := F) ρ) ?_)
    exact (leviRationalPointHomeomorph_apply_coe i ν I' x).symm.trans <|
      (congrArg Subtype.val hj).trans (coe_minimalLeviInclusion hG hi hν (rootSet i ν I') m)
  have hqx := h q x
  rw [hXi, hHeight] at hqx
  simpa only [x, j, inc, lowerLevelPacket] using hqx

end Lower

end Langlands.HarishChandraSchwartz.LowerPacket
