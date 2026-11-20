import Langlands.HarmonicAnalysis.HarishChandraSchwartz.DynamicOrbitDensityCompactChange
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakPositivePacketAssembly

/-! # Compact change for the standard-Levi weight and weak integral estimate -/

noncomputable section

set_option maxRecDepth 4096

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar

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

set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x}
set_option hygiene false in
local notation "νM" => RationalPointFamily.leviRationalNormCharacters i ν I

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] (mu : Measure (𝐌 ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)

set_option hygiene false in
local notation "Oπ" => discreteSeriesOrbit C hC mu νM (discreteSeriesClass C hC mu π hsq)

section Weight

variable {ζ : cocharacterLattice S}
  (hζ : IsStandardCocharacter i ν (RationalPointFamily.rootSet i ν I) ζ)
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (P : DynamicInducedOrbit.DensityPackage i ζ hRefl hCST hG
    (SmoothRep.pullback (standardLeviDynamicHomeomorph hG hi hν I hζ) π.obj))

/-- Evaluate the weight of a density package on the original standard-Levi orbit. -/
def standardLeviDensityPackageWeight : Oπ → ℂ :=
  standardLeviPlancherelWeight hG hi hν I hζ π C hC mu hsq hRefl hCST
    P.K P.hK P.hPK P.hOppK P.p P.q P.hDForward P.hneForward P.hDForwardΩ P.hDReverse
    P.hneReverse P.hDReverseΩ P.hD P.hne P.hirr P.hreg

variable (L : OpenSubgroup (rationalPoints G)) (hL : IsCompact (L : Set (rationalPoints G)))
  (hPL : ∀ g : rationalPoints G,
    ∃ p : parabolic (CommGroupScheme.groupHom ζ ≫ i), ∃ l : L,
      g = (p : rationalPoints G) * (l : rationalPoints G))
  (hOppL : ∀ g : rationalPoints G,
    ∃ p : oppositeParabolic (CommGroupScheme.groupHom ζ ≫ i), ∃ l : L,
      g = (p : rationalPoints G) * (l : rationalPoints G))

set_option maxHeartbeats 900000 in
/-- The new weight differs from the original by the constant density factor on the same orbit. -/
theorem standardLeviDensityPackageWeight_changeCompact (ω : Oπ) :
    standardLeviDensityPackageWeight hG hi hν I π C hC mu hsq hζ hRefl hCST
        (P.changeCompact L hL hPL hOppL) ω =
      (P.compactDensityScale L hL : ℂ) *
        standardLeviDensityPackageWeight hG hi hν I π C hC mu hsq hζ hRefl hCST P ω := by
  obtain ⟨z, rfl⟩ := (isOpenQuotientMap_discreteSeriesOrbitMap C hC mu νM
    (discreteSeriesClass C hC mu π hsq)).surjective ω
  unfold standardLeviDensityPackageWeight
  rw [standardLeviPlancherelWeight_orbitMap, standardLeviPlancherelWeight_orbitMap]
  exact P.changeCompact_weight L hL hPL hOppL hi.isSplitSubtorus.1
    (standardLeviCharacterRestrict hG hi hν I hζ z)

end Weight

section Weak

variable {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
  (I' : Finset (RationalPointFamily.SimpleRoot i ν))
  {A : CommGroupScheme (Spec (CommRingCat.of F))} {qA : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν (RationalPointFamily.rootSet i ν I') A qA)
  {n : ℕ} [Nonempty (Fin n)] (ρ : MatrixRepresentation G (Fin n))
  [Finite (discreteSeriesStabilizer C hC mu νM (discreteSeriesClass C hC mu π hsq))]
  (rhoX : Measure (unitaryUnramifiedCharacters νM))

set_option maxHeartbeats 1000000 in
private theorem rationalOrbitLevelWeakPacketRapid_const_mul (c : ℂ) (w : Oπ → ℂ)
    (hw : RationalOrbitLevelWeakPacketRapid hG hi hν I hKc hPK π C hC mu hsq I' hA ρ rhoX w) :
    RationalOrbitLevelWeakPacketRapid hG hi hν I hKc hPK π C hC mu hsq I' hA ρ rhoX
      (fun ω => c * w ω) := by
  intro H hHK r
  obtain ⟨t, d, hd⟩ := hw H hHK r
  refine ⟨t, ‖c‖₊ * d, fun q m hm => ?_⟩
  obtain ⟨hInt, hnorm⟩ := hd q m hm
  constructor
  · simpa only [mul_assoc] using hInt.const_mul c
  · simp only [mul_assoc c]
    rw [integral_const_mul, mul_left_comm _ c, norm_mul]
    simpa only [NNReal.coe_mul, coe_nnnorm, mul_assoc] using
      mul_le_mul_of_nonneg_left hnorm (norm_nonneg c)

variable {ζ : cocharacterLattice S}
  (hζ : IsStandardCocharacter i ν (RationalPointFamily.rootSet i ν I) ζ)
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (P : DynamicInducedOrbit.DensityPackage i ζ hRefl hCST hG
    (SmoothRep.pullback (standardLeviDynamicHomeomorph hG hi hν I hζ) π.obj))
  (L : OpenSubgroup (rationalPoints G)) (hL : IsCompact (L : Set (rationalPoints G)))
  (hPL : ∀ g : rationalPoints G,
    ∃ p : parabolic (CommGroupScheme.groupHom ζ ≫ i), ∃ l : L,
      g = (p : rationalPoints G) * (l : rationalPoints G))
  (hOppL : ∀ g : rationalPoints G,
    ∃ p : oppositeParabolic (CommGroupScheme.groupHom ζ ≫ i), ∃ l : L,
      g = (p : rationalPoints G) * (l : rationalPoints G))

set_option hygiene false in
local notation "newPackage" => P.changeCompact L hL hPL hOppL
set_option hygiene false in
local notation "weightOf[" Q "]" =>
  standardLeviDensityPackageWeight hG hi hν I π C hC mu hsq hζ hRefl hCST Q

set_option maxHeartbeats 1200000 in
/-- Transfer the integrability and weak integral bound at the changed
density normalization back to the original weight and character measure. -/
theorem rationalOrbitLevelWeakPacketRapid_of_densityCompactChange
    (hw : RationalOrbitLevelWeakPacketRapid hG hi hν I hKc hPK π C hC mu hsq I' hA ρ rhoX
      weightOf[newPackage]) :
    RationalOrbitLevelWeakPacketRapid hG hi hν I hKc hPK π C hC mu hsq I' hA ρ rhoX
      weightOf[P] := by
  let c : ℂ := (P.compactDensityScale L hL : ℂ)
  have hc : c ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (P.compactDensityScale_pos L hL hi.isSplitSubtorus.1).ne'
  have he : weightOf[P] = fun ω => c⁻¹ * weightOf[newPackage] ω := by
    funext ω
    have h := standardLeviDensityPackageWeight_changeCompact hG hi hν I π C hC mu hsq
      hζ hRefl hCST P L hL hPL hOppL ω
    change weightOf[newPackage] ω = c * weightOf[P] ω at h
    rw [h, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rw [he]
  exact rationalOrbitLevelWeakPacketRapid_const_mul hG hi hν I π C hC mu hsq
    hKc hPK I' hA ρ rhoX c⁻¹ weightOf[newPackage] hw

end Weak

end Langlands.HarishChandraSchwartz
