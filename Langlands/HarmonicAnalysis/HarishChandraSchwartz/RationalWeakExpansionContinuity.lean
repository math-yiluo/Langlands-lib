import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionTargets
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.DynamicInducedOrbitCoefficientContinuity

/-! # Continuity and integrability of the weighted weak term -/

noncomputable section

set_option maxRecDepth 8000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

namespace WeakExpansion

open DynamicOppositeStandardIntertwining RationalPointFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

local instance weakContinuityAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance weakContinuityLeviAffineHom (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J
local instance weakContinuityLeviAffine (J : Set (characterLattice T)) :
    IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom
local instance weakContinuityLeviFiniteType (J : Set (characterLattice T)) :
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
local notation "lowerCoefficient[" s "]" => DynamicInducedOrbit.inducedOrbitCoefficientMap (H := 𝐋)
  hM' (χ_ s) lowerKc[s] lowerPK[s] lowerπ[s] lowerC[s] lowerhC[s] lowerMu[s] lowerSq[s]
set_option hygiene false in
local notation "weakTerm" => rationalOrbitWeakConstantTerm hG hi hν I hKc hPK π CM hCM mu hsq I' hA
set_option hygiene false in
local notation "UpperSections" => rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π
set_option hygiene false in
local notation "lowerNormal[" s "]" => lowerCentral_normal hG hi hν I I' hζ (nₛ s) (hnₛ s) CM
set_option hygiene false in
local notation "lowerMeas[" s "]" => lowerQuotientMeasurableSpace hG hi hν I I' hζ (nₛ s) (hnₛ s) CM
set_option hygiene false in
local notation "lowerHaar[" s "]" => lowerMeasure_isHaarMeasure hG hi hν I I' hζ (nₛ s) (hnₛ s) CM mu

set_option maxHeartbeats 1300000 in
omit [IsAffine Tc.X.left] [(rationalPoints.map sc).range.Normal] in
/-- Lower orbit conjugation is continuous by its compatibility with the
actual open quotient parametrizations. -/
theorem continuous_lowerOrbitMap (s : Index) : Continuous lowerMap[s] := by
  let ω := discreteSeriesClass CM hCM mu π hsq
  let T := lowerCharacterConjugation hG hi hν I I' hζ (nₛ s) (hnₛ s)
  let f := discreteSeriesOrbitMap CM hCM mu νM ω
  let ω' := discreteSeriesClass lowerC[s] lowerhC[s] lowerMu[s] lowerπ[s] lowerSq[s]
  let f' := discreteSeriesOrbitMap lowerC[s] lowerhC[s] lowerMu[s] (leviNormCharacters (χ_ s)) ω'
  apply (isOpenQuotientMap_discreteSeriesOrbitMap CM hCM mu νM ω).isQuotientMap.continuous_iff.mpr
  have h : lowerMap[s] ∘ f = f' ∘ T :=
    funext (lowerOrbitMap_orbitMap hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM mu π hsq)
  change Continuous (lowerMap[s] ∘ f)
  rw [h]
  exact (continuous_discreteSeriesOrbitMap lowerC[s] lowerhC[s] lowerMu[s] _ ω').comp T.continuous

set_option maxHeartbeats 2200000 in
omit [IsAffine Tc.X.left] [(rationalPoints.map sc).range.Normal] in
private theorem continuous_lowerPlancherelWeight (s : Index) : Continuous lowerW[s] :=
  @DynamicInducedOrbit.continuous_orbitPlancherelWeight _ _ _ _ _ _ _ _ _
    (Standard.leviTorusHom i ν (rootSet i ν I'))
    (conjugatedCocharacter i ζ (nₛ s)) hRefl hCST hM' lowerπ[s]
    lowerC[s] lowerNormal[s] lowerhC[s] lowerMeas[s] lowerMu[s] lowerHaar[s]
    lowerSq[s] (PM s)

set_option maxHeartbeats 5200000 in
omit [IsAffine Tc.X.left] [(rationalPoints.map sc).range.Normal] in
private theorem continuous_lowerCoefficient_pullback (s : Index)
    (Ψ : LowerSections hG hi hν I I' hζ π hRefl hCST R PM s) (x : RationalPoint F 𝐋.X) :
    Continuous (fun ω : Oπ => lowerCoefficient[s] Ψ (lowerMap[s] ω) x) := by
  have h : Continuous (fun ω => lowerCoefficient[s] Ψ ω x) :=
    @DynamicInducedOrbit.continuous_inducedOrbitCoefficientMap F _ _ _ _ 𝐋 _ _ hM' (χ_ s)
      lowerK₀[s] lowerKc[s] lowerPK[s] lowerπ[s] lowerC[s] lowerNormal[s] lowerhC[s]
      lowerMeas[s] lowerMu[s] lowerHaar[s] lowerSq[s] Ψ x
  exact h.comp (continuous_lowerOrbitMap hG hi hν I I' hζ sc hs π mu hsq R s)

/-- The actual Plancherel-weighted weak constant term is continuous in the
original orbit variable at every lower-Levi point. -/
def WeightedWeakConstantTermContinuous : Prop :=
  ∀ (q : UpperSections) (m : standardLeviPoints i ν (rootSet i ν I')),
    Continuous (fun ω : Oπ => Wπ ω * weakTerm q ω m)

set_option maxHeartbeats 2600000 in
omit [IsAffine Tc.X.left] [(rationalPoints.map sc).range.Normal] in
/-- The pointwise weighted expansion expresses the weak term as a finite
sum of continuous lower weighted coefficients. -/
theorem weightedWeakConstantTermContinuous_of_expansion
    (hproper : ∃ α : SimpleRoot i ν, α ∉ I')
    (hspecial : IsSpecialVertexCompact ν hi K)
    (hlifts : LiftsInCompact I I' (K := K) R)
    (hN : SourceCompactNormalization hG hi hν I I' hζ (K := K) π hRefl hCST PG R PM)
    (hexp : WeightedWeakExpansionStatement hG hi hν I I' hζ hζ' hKc hPK sc hs π mu hsq
      hRefl hCST PG hA R PM) :
    WeightedWeakConstantTermContinuous hG hi hν I I' hζ hKc hPK sc hs π mu hsq
      hRefl hCST PG hA := by
  classical
  let : Fintype Index := @Fintype.ofFinite _ (finite_weylIndex i ν (rootSet i ν I) (rootSet i ν I') hG hi)
  intro q m
  obtain ⟨x, rfl⟩ := (leviRationalPointHomeomorph i ν I').surjective m
  obtain ⟨_, Ψ, _, hformula⟩ := hexp hproper hspecial hlifts hN q
  let f (s : Index) (ω : Oπ) := lowerW[s] (lowerMap[s] ω) * lowerCoefficient[s] (Ψ s) (lowerMap[s] ω) x
  have hf (s : Index) : Continuous (f s) := by
    have hm := continuous_lowerOrbitMap hG hi hν I I' hζ sc hs π mu hsq R s
    exact ((continuous_lowerPlancherelWeight hG hi hν I I' hζ sc hs π mu hsq
      hRefl hCST R PM s).comp hm).mul (continuous_lowerCoefficient_pullback hG hi hν I I' hζ
        sc hs π mu hsq hRefl hCST R PM s (Ψ s) x)
  have hEq : (fun ω : Oπ => Wπ ω * weakTerm q ω (leviRationalPointHomeomorph i ν I' x)) =
      fun ω => ∑ s, f s ω := by
    funext ω
    with_reducible exact hformula ω x
  rw [hEq]
  exact continuous_finsetSum _ fun s _ => hf s

set_option maxHeartbeats 1400000 in
/-- Continuity on the finite compact original orbit gives Bochner
integrability against the source-normalized orbit measure. -/
theorem integrable_weightedWeakConstantTerm_of_continuous
    (hc : WeightedWeakConstantTermContinuous hG hi hν I I' hζ hKc hPK sc hs π mu hsq
      hRefl hCST PG hA) :
    letI := finite_standardLeviDiscreteSeriesStabilizer I sc hs hindex mu
      (discreteSeriesClass CM hCM mu π hsq)
    ∀ (q : UpperSections) (m : standardLeviPoints i ν (rootSet i ν I')),
      Integrable (fun ω : Oπ => Wπ ω * weakTerm q ω m)
        (discreteSeriesOrbitMeasure νM CM hCM mu (discreteSeriesClass CM hCM mu π hsq)
          (standardLeviUnitaryUnramifiedCharacterHaar I sc hs hindex)) := by
  let ω := discreteSeriesClass CM hCM mu π hsq
  let := finite_standardLeviDiscreteSeriesStabilizer I sc hs hindex mu ω
  let : CompactSpace (unitaryUnramifiedCharacters νM) :=
    (leviRationalUnitaryCoordinates hG hi hν I).toHomeomorph.symm.compactSpace
  let := compactSpace_discreteSeriesOrbit CM hCM mu νM ω
  let := isFiniteMeasure_standardLeviOrbitMeasure I sc hs hindex mu ω
  intro q m
  exact (hc q m).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

end WeakExpansion

end Langlands.HarishChandraSchwartz
