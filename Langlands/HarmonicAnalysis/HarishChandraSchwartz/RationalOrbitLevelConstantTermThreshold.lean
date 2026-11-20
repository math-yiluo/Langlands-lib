import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitSectionLevelFiberGenerators
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitCompactConstantTerm

/-! # Constant-term thresholds uniform over an entire section level -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (RationalPointFamily.SimpleRoot i ν))
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))

set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x}
set_option hygiene false in
local notation "νM" => RationalPointFamily.leviRationalNormCharacters i ν I

set_option hygiene false in
local notation "decomp" => isSemidirectDecomposition_standard hG hi hν
  (RationalPointFamily.rootSet_subset i ν I)
set_option hygiene false in
local notation "closedU" => isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)

set_option hygiene false in
local notation "closedP" => isClosed_standardParabolicPoints_rootSet hG hi hν I
set_option hygiene false in
local notation "factorization" => factorization_subtype
  (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
set_option hygiene false in
local notation "hnorm" => RationalPointFamily.continuous_leviRationalNormCharacters i ν I
set_option hygiene false in
local notation "hprojection" => continuous_projection_standard hG hi hν
  (RationalPointFamily.rootSet_subset i ν I) decomp
set_option hygiene false in
local notation "coordinates" => (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv
set_option hygiene false in
local notation "J" => Fin (rationalImageRank (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I)))

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] (mu : Measure (𝐌 ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)

variable (I' : Finset (RationalPointFamily.SimpleRoot i ν))
  {A : CommGroupScheme (Spec (CommRingCat.of F))} {qA : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν (RationalPointFamily.rootSet i ν I') A qA)
  [hStab : Finite (discreteSeriesStabilizer C hC mu νM (discreteSeriesClass C hC mu π hsq))]
  {ζ : cocharacterLattice S}
  (hζ : IsStandardCocharacter i ν (RationalPointFamily.rootSet i ν I') ζ)
  {K₀ : Subgroup (rationalPoints G)} {B : Set (Subgroup (rationalPoints G))}
  (hB : CompactOpenNormalBasis K₀ B)
  (hmem : ∀ K' ∈ B, StandardParabolicBasisMember i ν (RationalPointFamily.rootSet i ν I') qA K')

set_option hygiene false in
local notation "Picture" => ProductInducedCompactPicture decomp K π.obj
set_option hygiene false in
local notation "SectionLevel" => OrbitSectionLevel νM π coordinates decomp closedU K closedP hKc
  hnorm hprojection factorization
set_option hygiene false in
local notation "includeLevel" => OrbitSectionLevel.toSections νM π coordinates decomp closedU K closedP
  hKc hnorm hprojection factorization
set_option hygiene false in
local notation "Fixed" H => orbitSectionFixedCoefficients decomp K π H
set_option hygiene false in
local notation "fixedRestriction" => orbitSectionLevelFixedRestriction decomp K π νM coordinates
  closedU closedP hKc hnorm hprojection factorization
set_option hygiene false in
local notation "J'" => RationalPointFamily.rootSet i ν I'
set_option hygiene false in
local notation "incM" => minimalLeviInclusion hG hi hν J'
set_option hygiene false in
local notation "Oπ" => discreteSeriesOrbit C hC mu νM (discreteSeriesClass C hC mu π hsq)
set_option hygiene false in
local notation "paramOrbit" => discreteSeriesOrbitMap C hC mu νM (discreteSeriesClass C hC mu π hsq)
set_option hygiene false in
local notation "orbitCoefficient" => rationalInducedOrbitCoefficientMap hG hi hν I hKc hPK π C hC mu hsq
set_option hygiene false in
local notation "orbitCT" => rationalOrbitConstantTerm hG hi hν I hKc hPK π C hC mu hsq I' hA
set_option hygiene false in
local notation "compactCT" => rationalOrbitCompactConstantTerm hG hi hν I hKc hPK
  π C hC mu hsq I' hA hζ hB hmem
set_option hygiene false in
local notation "thresholdRegion" => rationalConstantTermThresholdRegion hG hi hν J'
set_option hygiene false in
local notation "halfMod" => standardHalfModulus i ν J'
set_option hygiene false in
local notation "ambientUnimodular" => fun g =>
  RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g
set_option hygiene false in
local notation "parabolicModulus" => modularCharacter_standardParabolicPoints hG hi hν I rfl
  (RationalPointFamily.rootSet_subset i ν I)

/-- On one threshold region, all sections at the given level satisfy the
normalized actual-point constant-term identity. -/
def RationalOrbitLevelConstantTermThreshold : Prop :=
  ∀ (H : OpenSubgroup (rationalPoints G)), H ≤ K →
    ∃ t > 0, ∀ (q : SectionLevel H) (ω : Oπ) (m : standardLeviPoints i ν ∅),
      m ∈ thresholdRegion t →
      orbitCoefficient (includeLevel H q) ω m = halfMod (incM m) * orbitCT (includeLevel H q) ω (incM m)

include hStab hζ hB hmem in
/-- The per-section actual constant-term thresholds yield a common threshold
for an entire fixed level by the finite smooth tests of its compact fibers. -/
theorem rationalOrbitLevelConstantTermThreshold_of_perSection
    (hthreshold : ∀ ψ : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π,
      ∃ t > 0, ∀ (ω : Oπ) (m : standardLeviPoints i ν ∅), m ∈ thresholdRegion t →
        orbitCoefficient ψ ω m = halfMod (incM m) * orbitCT ψ ω (incM m)) :
    RationalOrbitLevelConstantTermThreshold hG hi hν I hKc hPK π C hC mu hsq I' hA := by
  classical
  intro H hHK
  let := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  let := Finite.of_injective _ (unitaryClassStabilizerEquivDiscreteSeries νM π C hC mu hsq).injective
  let hcofinal : CompactOpenCofinal 𝐌 := compactOpenCofinal_of_isClosed
    (isClosed_standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))
  let := finiteDimensional_orbitSectionFixedCoefficients decomp K π hKc hcofinal H hHK
  let b := Module.finBasis ℂ (Fixed H)
  let coef := unitaryOrbitCompactCoefficient decomp closedU closedP K hKc factorization νM π
    hnorm hprojection coordinates ambientUnimodular parabolicModulus
  let ct (z : J → Circle) (m : standardLeviPoints i ν ∅) : Picture →ₗ[ℂ] ℂ :=
    ((LinearMap.proj (incM m)).comp (weakExponentSpace (standardComponentHom hA) ⊔
      positiveExponentSpace (standardComponentHom hA)).subtype).comp (compactCT z)
  let L (z : J → Circle) (m : standardLeviPoints i ν ∅) : (Fixed H) →ₗ[ℂ] ℂ :=
    (coef z m - halfMod (incM m) • ct z m).comp (Fixed H).subtype
  have hL (q : SectionLevel H) (z : J → Circle) (m : standardLeviPoints i ν ∅) :
      L z m (fixedRestriction H hHK q z) =
        orbitCoefficient (includeLevel H q) (paramOrbit ((coordinates).symm z)) m -
          halfMod (incM m) * orbitCT (includeLevel H q) (paramOrbit ((coordinates).symm z)) (incM m) := by
    have hc := unitaryOrbitCompactCoefficient_restriction decomp closedU closedP K hKc factorization νM π
      hnorm hprojection coordinates ambientUnimodular parabolicModulus C hC mu hsq (includeLevel H q) z
      (m : rationalPoints G)
    have ht := congrFun (rationalOrbitCompactConstantTerm_restriction hG hi hν I hKc hPK
      π C hC mu hsq I' hA hζ hB hmem (includeLevel H q) z) (incM m)
    exact congrArg₂ (fun a b : ℂ => a - halfMod (incM m) * b) hc ht
  have hanti : Antitone thresholdRegion := by
    intro a b hab m hm
    exact ⟨hm.1, fun α hα => hab.trans (hm.2 α hα)⟩
  have hzero (q : SectionLevel H) : ∃ t > 0, ∀ z m, m ∈ thresholdRegion t →
      L z m (fixedRestriction H hHK q z) = 0 := by
    let ψ : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π := includeLevel H q
    have hp := hthreshold ψ
    refine ⟨hp.choose, hp.choose_spec.1, fun z m hm => ?_⟩
    exact (hL q z m).trans (sub_eq_zero.mpr (hp.choose_spec.2 (paramOrbit ((coordinates).symm z)) m hm))
  have hgen := exists_finite_orbitSectionLevel_fiber_generators decomp closedU closedP K hKc
    factorization νM π hnorm hprojection coordinates H hHK b
  obtain ⟨t, ht, hLzero⟩ := exists_uniform_fiber_zero_threshold decomp closedU closedP K hKc
    factorization νM π hnorm hprojection coordinates H hHK b hgen L thresholdRegion hanti hzero
  refine ⟨t, ht, fun q ω m hm => ?_⟩
  obtain ⟨χ, rfl⟩ := (isOpenQuotientMap_discreteSeriesOrbitMap C hC mu νM
    (discreteSeriesClass C hC mu π hsq)).surjective ω
  let z := (coordinates) χ
  have he : (coordinates).symm z = χ := (coordinates).symm_apply_apply χ
  have hz := congrArg (fun T : (Fixed H) →ₗ[ℂ] ℂ => T (fixedRestriction H hHK q z)) (hLzero z m hm)
  have heq := sub_eq_zero.mp ((hL q z m).symm.trans hz)
  simpa only [he] using heq

end Langlands.HarishChandraSchwartz
