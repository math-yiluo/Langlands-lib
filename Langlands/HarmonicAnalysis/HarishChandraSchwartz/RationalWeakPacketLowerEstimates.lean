import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionLevelControl
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionContinuity
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakPositivePacketAssembly

/-! # Summing actual lower packet estimates for the weighted weak term -/

noncomputable section

set_option maxRecDepth 10000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

namespace WeakExpansion

open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar RationalPointFamily
open Langlands.Induction

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

local instance weakPacketEstimateAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance weakPacketEstimateLeviAffineHom (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J
local instance weakPacketEstimateLeviAffine (J : Set (characterLattice T)) :
    IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom
local instance weakPacketEstimateLeviFiniteType (J : Set (characterLattice T)) :
    LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom :=
  leviScheme_locallyOfFiniteType i ν J

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

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I I' : Finset (SimpleRoot i ν))
  {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  {ζ' : cocharacterLattice T} (hζ' : IsStandardCocharacter i ν (rootSet i ν I') ζ')

-- `M_I(F)` as a subtype of `G(F)`, written as in `rationalInducedSmoothOrbitSections`.
set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}
set_option hygiene false in
local notation "νM" => leviRationalNormCharacters i ν I
set_option hygiene false in
local notation "eM" => (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv

variable {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))

set_option hygiene false in
local notation "𝐋I" => Standard.leviScheme i ν (rootSet i ν I)
set_option hygiene false in
local notation "𝐋" => lowerAmbient i ν (rootSet i ν I')
set_option hygiene false in
local notation "hM'" => lowerAmbient_isConnectedReductive hG hi hν I'

variable {Tc : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine Tc.X.left]
  (sc : Tc.toGrp ⟶ 𝐋I) (hs : IsSplitComponent sc)
  (hindex : (RenardCartan.splitValuationImage sc).FiniteIndex)

set_option hygiene false in
local notation "CM" => rationalLeviSplitCenter I sc
set_option hygiene false in
local notation "hCM" => rationalLeviSplitCenter_le_center I sc hs

variable [(CM).Normal] [(rationalPoints.map sc).range.Normal]
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  [MeasurableSpace (𝐌 ⧸ CM)] [BorelSpace (𝐌 ⧸ CM)]
  (mu : Measure (𝐌 ⧸ CM)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup CM hCM π.obj.representation mu)
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (PG : DynamicInducedOrbit.DensityPackage i ζ hRefl hCST hG
    (SmoothRep.pullback (standardLeviDynamicHomeomorph hG hi hν I hζ) π.obj))
  {A : CommGroupScheme (Spec (CommRingCat.of F))} {qA : A.toGrp ⟶ T.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν (rootSet i ν I') A qA)
  (R : Representatives i ν (rootSet i ν I) (rootSet i ν I'))
  (PM : ∀ s : WeylIndex i ν (rootSet i ν I) (rootSet i ν I'),
    LowerDensityPackage hG hi hν I I' hζ (R.normalizer s) (R.levi_le s) π hRefl hCST)

set_option hygiene false in
local notation "Oπ" => discreteSeriesOrbit CM hCM mu νM (discreteSeriesClass CM hCM mu π hsq)
set_option hygiene false in
local notation "Wπ" => standardLeviPlancherelWeight hG hi hν I hζ π CM hCM mu hsq hRefl hCST
  PG.K PG.hK PG.hPK PG.hOppK PG.p PG.q PG.hDForward PG.hneForward PG.hDForwardΩ PG.hDReverse
  PG.hneReverse PG.hDReverseΩ PG.hD PG.hne PG.hirr PG.hreg
set_option hygiene false in
local notation "χ_" s => lowerCocharacter i ν (rootSet i ν I') ζ (R.normalizer s)

set_option hygiene false in
local notation "Index" => WeylIndex i ν (rootSet i ν I) (rootSet i ν I')
set_option hygiene false in
local notation "nₛ" => R.normalizer
set_option hygiene false in
local notation "hnₛ" => R.levi_le
set_option hygiene false in
local notation "lowerMap[" s "]" => lowerOrbitMap hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM mu π hsq
set_option hygiene false in
local notation "lowerW[" s "]" => lowerPlancherelWeight hG hi hν I I' hζ (nₛ s) (hnₛ s)
  CM hCM mu π hsq hRefl hCST (PM s)
set_option hygiene false in
local notation "lowerC[" s "]" => lowerCentral hG hi hν I I' hζ (nₛ s) (hnₛ s) CM
set_option hygiene false in
local notation "lowerhC[" s "]" => lowerCentral_le_center hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM
set_option hygiene false in
local notation "lowerMu[" s "]" => lowerMeasure hG hi hν I I' hζ (nₛ s) (hnₛ s) CM mu
set_option hygiene false in
local notation "lowerπ[" s "]" => lowerRepresentation hG hi hν I I' hζ (nₛ s) (hnₛ s) π
set_option hygiene false in
local notation "lowerSq[" s "]" => lowerRepresentation_isSquareIntegrable hG hi hν I I' hζ (nₛ s) (hnₛ s)
  CM hCM mu π hsq
set_option hygiene false in
local notation "lowerKc[" s "]" => lowerK_isCompact hG hi hν I I' hζ (nₛ s) (hnₛ s) hRefl hCST π (PM s)
set_option hygiene false in
local notation "lowerK₀[" s "]" => lowerK hG hi hν I I' hζ (nₛ s) (hnₛ s) hRefl hCST π (PM s)
set_option hygiene false in
local notation "lowerPK[" s "]" => lowerPackage_iwasawa hG hi hν I I' hζ (nₛ s) (hnₛ s) hRefl hCST π (PM s)
set_option hygiene false in
local notation "roots" => rootSet i ν I'
set_option hygiene false in
local notation "hNType" => SourceCompactNormalization hG hi hν I I' hζ (K := K) π hRefl hCST PG R PM
set_option hygiene false in
local notation "rhoX" => standardLeviUnitaryUnramifiedCharacterHaar I sc hs hindex
set_option hygiene false in
local notation "omegaπ" => discreteSeriesClass CM hCM mu π hsq
set_option hygiene false in
local notation "finiteUpper" => finite_standardLeviDiscreteSeriesStabilizer I sc hs hindex mu omegaπ
set_option hygiene false in
local notation "dO" => discreteSeriesOrbitMeasure νM CM hCM mu omegaπ rhoX
set_option hygiene false in
local notation "weakTerm" => rationalOrbitWeakConstantTerm hG hi hν I hKc hPK π CM hCM mu hsq I' hA
set_option hygiene false in
local notation "incM" => minimalLeviInclusion hG hi hν roots
set_option hygiene false in
local notation "lowerPoint" => fun m => (leviRationalPointHomeomorph i ν I').symm (incM m)
set_option hygiene false in
local notation "half" => fun m => standardHalfModulus i ν roots (incM m)

set_option hygiene false in
local notation "νL[" s "]" => leviNormCharacters (χ_ s)
set_option hygiene false in
local notation "lowerρ[" s "]" => lowerCharacterMeasure hG hi hν I I' hζ (nₛ s) (hnₛ s) rhoX
set_option maxHeartbeats 1800000 in
private abbrev sourceNormalizedLowerPacket (s : Index) :=
  letI := finiteUpper
  letI := finite_lowerStabilizer hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM mu π hsq
  DynamicInducedOrbit.inducedOrbitWavePacket (H := 𝐋) hM' (χ_ s) lowerKc[s] lowerPK[s]
    lowerπ[s] lowerC[s] lowerhC[s] lowerMu[s] lowerSq[s] lowerρ[s] lowerW[s]

set_option hygiene false in
local notation "lowerPacket[" s "]" => sourceNormalizedLowerPacket hG hi hν I I' hζ sc hs hindex
  π mu hsq hRefl hCST R PM s
set_option hygiene false in
local notation "DL[" s "]" => decomposition (χ_ s)
set_option hygiene false in
local notation "UL[" s "]" => radical_isClosed (χ_ s)
set_option hygiene false in
local notation "PL[" s "]" => parabolic_isClosed (χ_ s)
set_option hygiene false in
local notation "NL[" s "]" => DynamicInducedOrbit.leviNormCharacters_continuous (χ_ s)
set_option hygiene false in
local notation "RL[" s "]" => projection_continuous (χ_ s)
set_option hygiene false in
local notation "eL[" s "]" => (DynamicInducedOrbit.leviUnitaryCoordinates (H := 𝐋) hM' (χ_ s)).toMulEquiv
set_option hygiene false in
local notation "LowerLevel[" s "," H "]" => OrbitSectionLevel νL[s] lowerπ[s] eL[s] DL[s] UL[s]
  lowerK₀[s] PL[s] lowerKc[s] NL[s] RL[s] lowerPK[s] H
set_option hygiene false in
local notation "lowerInclude[" s "," H "]" => OrbitSectionLevel.toSections νL[s] lowerπ[s] eL[s] DL[s] UL[s]
  lowerK₀[s] PL[s] lowerKc[s] NL[s] RL[s] lowerPK[s] H
set_option hygiene false in
local notation "lowerSeminorm[" s "," H "]" => OrbitSectionLevel.seminormFamily νL[s] lowerπ[s] eL[s] DL[s] UL[s]
  lowerK₀[s] PL[s] lowerKc[s] NL[s] RL[s] lowerPK[s] H
set_option hygiene false in
local notation "LowerDerivativeIndex[" s "]" => List (Fin (rationalImageRank (parameterScheme (χ_ s)))) ×
  Module.Dual ℂ (ProductInducedCompactPicture DL[s] lowerK₀[s] (lowerπ[s]).obj)

set_option hygiene false in
local notation "DU" => isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I)
set_option hygiene false in
local notation "UU" => isClosed_standardUnipotentPoints i ν (rootSet i ν I)
set_option hygiene false in
local notation "PU" => isClosed_standardParabolicPoints_rootSet hG hi hν I
set_option hygiene false in
local notation "NU" => continuous_leviRationalNormCharacters i ν I
set_option hygiene false in
local notation "RU" => continuous_projection_standard hG hi hν (rootSet_subset i ν I) DU
set_option hygiene false in
local notation "FU" => factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
set_option hygiene false in
local notation "UpperLevel[" H "]" => OrbitSectionLevel νM π eM DU UU K PU hKc NU RU FU H
set_option hygiene false in
local notation "upperInclude[" H "]" => OrbitSectionLevel.toSections νM π eM DU UU K PU hKc NU RU FU H
set_option hygiene false in
local notation "upperSeminorm[" H "]" => OrbitSectionLevel.seminormFamily νM π eM DU UU K PU hKc NU RU FU H
set_option hygiene false in
local notation "UpperDerivativeIndex" =>
  List (Fin (rationalImageRank 𝐋I)) × Module.Dual ℂ (ProductInducedCompactPicture DU K π.obj)

variable (hMK : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν roots))
  ((K : Subgroup (rationalPoints G)).subgroupOf (standardLeviPoints i ν roots)))
  {D : ℕ} [Nonempty (Fin D)] (ρ : MatrixRepresentation G (Fin D))

set_option hygiene false in
local notation "XiL" => fun m => rationalLeviXi hKc hMK (incM m)
set_option hygiene false in
local notation "XiU" => fun (m : standardLeviPoints i ν ∅) => rationalXi hKc hPK (m : rationalPoints G)
set_option hygiene false in
local notation "heightFactor[" r "," m "]" => (1 + rationalHeight (F := F) ρ (m : rationalPoints G)) ^ (-r)

set_option maxHeartbeats 1800000 in
/-- Lower packet estimates with the actual measures and ambient matrix height,
required on the images of full minimal closed chamber points. -/
def LowerDynamicPacketChamberEstimates : Prop :=
  letI := finiteUpper
  ∀ (s : Index) (H : OpenSubgroup (RationalPoint F 𝐋.X)), H ≤ lowerK₀[s] → ∀ r : ℝ,
    ∃ t : Finset LowerDerivativeIndex[s], ∃ c : ℝ≥0,
      ∀ (q : LowerLevel[s, H]) (m : standardLeviPoints i ν ∅),
        m ∈ rationalMinimalClosedChamber hG hi hν →
        ‖lowerPacket[s] (lowerInclude[s, H] q) (lowerPoint m)‖ ≤
          (c : ℝ) * (t.sup lowerSeminorm[s, H]) q * (XiL m * heightFactor[r, m])

set_option hygiene false in
local notation "lowerEstimates" => LowerDynamicPacketChamberEstimates hG hi hν I I' hζ hKc
  sc hs hindex π mu hsq hRefl hCST R PM hMK ρ
set_option hygiene false in
local notation "weakEstimates" => RationalOrbitLevelWeakPacketRapid hG hi hν I hKc hPK π CM hCM mu hsq
  I' hA ρ rhoX Wπ

set_option maxHeartbeats 5000000 in
/-- The actual weighted weak integral obeys the original finite derivative
bound if all lower packets do, using the weighted expansion and packet identity. -/
theorem rationalOrbitLevelWeakPacketRapid_of_lowerEstimates
    (hproper : ∃ α : SimpleRoot i ν, α ∉ I')
    (hspecial : IsSpecialVertexCompact ν hi K)
    (hlifts : LiftsInCompact I I' (K := K) R)
    (hN : hNType)
    (hexp : WeightedWeakExpansionStatement hG hi hν I I' hζ hζ' hKc hPK sc hs π mu hsq
      hRefl hCST PG hA R PM)
    (hpacket : WeightedPacketIdentityStatement hG hi hν I I' hζ hζ' hKc hPK sc hs hindex π mu hsq
      hRefl hCST PG hA R PM)
    (hXi : HasRationalLeviXiHalfModulusComparison hG hi hν hKc hPK hMK)
    (hlower : lowerEstimates) : letI := finiteUpper; weakEstimates := by
  classical
  let := finiteUpper
  let : Fintype Index := @Fintype.ofFinite _ (finite_weylIndex i ν (rootSet i ν I) roots hG hi)
  have hc := weightedWeakConstantTermContinuous_of_expansion hG hi hν I I' hζ hζ' hKc hPK
    sc hs π mu hsq hRefl hCST PG hA R PM hproper hspecial hlifts hN hexp
  have hInt := integrable_weightedWeakConstantTerm_of_continuous hG hi hν I I' hζ hKc hPK
    sc hs hindex π mu hsq hRefl hCST PG hA hc
  obtain ⟨B, hB, hXi⟩ := hXi
  intro H hHK r
  choose E Ψ hΨ hidentity using fun q : UpperLevel[H] =>
    hpacket hproper hspecial hlifts hN (upperInclude[H] q)
  have hlevel (s : Index) := hasWeightedCSectionLevelControl_of_weightedCSection
    hG hi hν I I' hζ hζ' hKc hPK π (nₛ s) (hnₛ s) hRefl hCST PG (PM s) (hN s)
    H hHK (E 0 s) (fun q => Ψ q s) (fun q => isWeightedCSection_of_extension
      hG hi hν I I' hζ hζ' hKc hPK π (nₛ s) (hnₛ s) hRefl hCST PG (PM s) (hN s)
      (E 0 s) (E q s) (upperInclude[H] q) (Ψ q s) (hΨ q s))
  choose L hLK lift hlift hseminorm using hlevel
  choose tLower cLower hbound using fun s : Index => hlower s (L s) (hLK s) r
  choose t c hcontrol using fun s : Index => hseminorm s (tLower s)
  let S := Finset.univ.biUnion t
  let C : ℝ≥0 := ∑ s : Index, cLower s * c s
  refine ⟨S, ⟨B, hB.le⟩ * C, fun q m hm => ⟨hInt (upperInclude[H] q) (incM m), ?_⟩⟩
  let p : ℝ := (S.sup upperSeminorm[H]) q
  let b : ℝ := XiL m * heightFactor[r, m]
  have hp : 0 ≤ p := apply_nonneg _ _
  have hheight : 0 ≤ heightFactor[r, m] := Real.rpow_nonneg (by linarith [rationalHeight_nonneg ρ (m : rationalPoints G)]) _
  have hb : 0 ≤ b := mul_nonneg (rationalLeviXi_nonneg hKc hMK (incM m)) hheight
  have hterm (s : Index) : ‖lowerPacket[s] (Ψ q s) (lowerPoint m)‖ ≤ ((cLower s * c s : ℝ≥0) : ℝ) * p * b := by
    have hs : t s ⊆ S := fun x hx => Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ s, hx⟩
    have hsup : (t s).sup upperSeminorm[H] ≤ S.sup upperSeminorm[H] := Finset.sup_mono hs
    have hctrl := (hcontrol s q).trans (mul_le_mul_of_nonneg_left (hsup q) (c s).coe_nonneg)
    have h := hbound s (lift s q) m hm
    rw [hlift s q] at h
    exact h.trans (by
      simpa only [NNReal.coe_mul, mul_assoc] using
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hctrl (cLower s).coe_nonneg) hb)
  have hsum : ‖∑ s : Index, lowerPacket[s] (Ψ q s) (lowerPoint m)‖ ≤ (C : ℝ) * p * b := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun s _ => hterm s).trans ?_)
    simp only [C, NNReal.coe_sum, Finset.sum_mul]
    exact le_rfl
  have hEq : (∫ ω, Wπ ω * weakTerm (upperInclude[H] q) ω (incM m) ∂dO) =
      ∑ s : Index, lowerPacket[s] (Ψ q s) (lowerPoint m) := by
    have h := hidentity q (lowerPoint m)
    refine Eq.trans ?_ h
    apply integral_congr_ae
    filter_upwards [] with w
    have hx : leviRationalPointHomeomorph i ν I' (lowerPoint m) = incM m :=
      (leviRationalPointHomeomorph i ν I').apply_symm_apply _
    exact congrArg (fun x => Wπ w * weakTerm (upperInclude[H] q) w x) hx.symm
  rw [hEq, norm_mul]
  calc
    _ ≤ ‖half m‖ * ((C : ℝ) * p * b) := mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = (‖half m‖ * XiL m) * ((C : ℝ) * p * heightFactor[r, m]) := by dsimp [b]; ring
    _ ≤ (B * XiU m) * ((C : ℝ) * p * heightFactor[r, m]) :=
      mul_le_mul_of_nonneg_right (hXi m hm) (mul_nonneg (mul_nonneg C.coe_nonneg hp) hheight)
    _ = _ := by
      change (B * XiU m) * ((C : ℝ) * p * heightFactor[r, m]) =
        (B * (C : ℝ)) * p * (XiU m * heightFactor[r, m])
      ring

end WeakExpansion

end Langlands.HarishChandraSchwartz
