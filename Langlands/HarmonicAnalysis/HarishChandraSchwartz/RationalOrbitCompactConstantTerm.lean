import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ConstantTermLinearProjection
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitConstantTermExistenceProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitSectionLevelCoefficientBound
import Langlands.Representation.Plancherel.SmoothFamilyPrescribedValues

/-! # Compact fiber maps for the actual orbit constant term -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
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

set_option hygiene false in
local notation "Picture" => ProductInducedCompactPicture decomp K π.obj
set_option hygiene false in
local notation "Sections" => rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π
set_option hygiene false in
local notation "restriction" => productInducedSmoothOrbitCompactRestriction
  decomp closedU νM π K closedP hKc hnorm hprojection factorization coordinates
set_option hygiene false in
local notation "orbitCoefficient" => rationalInducedOrbitCoefficientMap hG hi hν I hKc hPK π C hC mu hsq
set_option hygiene false in
local notation "compactCoefficient" =>
  (haveI := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  unitaryOrbitCompactCoefficient decomp closedU closedP K hKc factorization νM π hnorm hprojection coordinates
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl (RationalPointFamily.rootSet_subset i ν I)))
set_option hygiene false in
local notation "omega" z => discreteSeriesOrbitMap C hC mu νM (discreteSeriesClass C hC mu π hsq)
  ((coordinates).symm z)

private theorem compactCoefficient_restriction_rational (q : Sections) (z : J → Circle) :
    (fun g => compactCoefficient z g (restriction q z)) =
      fun g => orbitCoefficient q (omega z) g := by
  let := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  funext g
  have he := unitaryOrbitCompactCoefficient_restriction decomp closedU closedP K hKc
    factorization νM π hnorm hprojection coordinates
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl (RationalPointFamily.rootSet_subset i ν I))
    C hC mu hsq q z g
  with_reducible_and_instances exact he

variable (I' : Finset (RationalPointFamily.SimpleRoot i ν))
  {A : CommGroupScheme (Spec (CommRingCat.of F))} {qA : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν (RationalPointFamily.rootSet i ν I') A qA)
  [hStab : Finite (discreteSeriesStabilizer C hC mu νM (discreteSeriesClass C hC mu π hsq))]
  {ζ : cocharacterLattice S}
  (hζ : IsStandardCocharacter i ν (RationalPointFamily.rootSet i ν I') ζ)
  {K₀ : Subgroup (rationalPoints G)} {B : Set (Subgroup (rationalPoints G))}
  (hB : CompactOpenNormalBasis K₀ B)
  (hmem : ∀ K' ∈ B, StandardParabolicBasisMember i ν (RationalPointFamily.rootSet i ν I') qA K')

include hStab hζ hB hmem in
private theorem hasStandardConstantTerm_compactCoefficient (z : J → Circle) (v : Picture) :
    HasStandardConstantTerm hA (fun g => compactCoefficient z g v) := by
  let := Finite.of_injective _ (unitaryClassStabilizerEquivDiscreteSeries νM π C hC mu hsq).injective
  let E := productInducedCompactEquiv νM decomp K closedP hKc hnorm hprojection closedU factorization
    (unitaryTorusParameter νM coordinates z) π.obj
  obtain ⟨r, hr, hval⟩ := exists_mem_productInducedSmoothOrbitSections_eval_eq νM π coordinates
    decomp closedU K closedP hKc hnorm hprojection factorization z (E.symm v)
  let q : Sections := ⟨r, hr⟩
  have hq : restriction q z = v := by
    change E (r (unitaryOrbitParameterRepresentative νM π coordinates z)) = v
    rw [hval, E.apply_symm_apply]
  have he := compactCoefficient_restriction_rational hG hi hν I hKc hPK π C hC mu hsq q z
  have hc := rationalOrbitConstantTermExistence hG hi hν I hKc hPK π C hC mu hsq I' hA
    hζ hB hmem q (omega z)
  rw [hq] at he
  exact he.symm ▸ hc

set_option hygiene false in
local notation "termDomain" => standardConstantTermDomain hA
set_option hygiene false in
local notation "exponentSum" => weakExponentSpace (standardComponentHom hA) ⊔
  positiveExponentSpace (standardComponentHom hA)
set_option hygiene false in
local notation "𝐌'" => standardLeviPoints i ν (RationalPointFamily.rootSet i ν I')

/-- At each unitary parameter, the normalized constant term acts linearly on the
actual compact fiber of the inducing coefficient space. -/
def rationalOrbitCompactConstantTerm (z : J → Circle) : Picture →ₗ[ℂ]
    (exponentSum : Submodule ℂ (𝐌' → ℂ)) :=
  (standardConstantTermLinear hA hi hζ).comp ((LinearMap.pi (compactCoefficient z)).codRestrict
    termDomain (hasStandardConstantTerm_compactCoefficient hG hi hν I hKc hPK π C hC mu hsq
      I' hA hζ hB hmem z))

set_option hygiene false in
local notation "compactConstantTerm" => rationalOrbitCompactConstantTerm hG hi hν I hKc hPK
  π C hC mu hsq I' hA hζ hB hmem

/-- The positive constant term is a linear map of the actual compact fiber. -/
def rationalOrbitCompactPositiveConstantTerm (z : J → Circle) : Picture →ₗ[ℂ] (𝐌' → ℂ) :=
  (positivePartLinear (standardComponentHom hA)).comp (compactConstantTerm z)

/-- The compact constant term recovers the original orbit constant term on a
section's compact restriction. -/
theorem rationalOrbitCompactConstantTerm_restriction (q : Sections) (z : J → Circle) :
    (compactConstantTerm z (restriction q z)).val =
      rationalOrbitConstantTerm hG hi hν I hKc hPK π C hC mu hsq I' hA q (omega z) := by
  change standardConstantTerm hA (fun g => compactCoefficient z g (restriction q z)) = _
  exact congrArg (standardConstantTerm hA)
    (compactCoefficient_restriction_rational hG hi hν I hKc hPK π C hC mu hsq q z)

/-- Positive projection of the compact constant term recovers the actual
positive part on a section's compact restriction. -/
theorem rationalOrbitCompactPositiveConstantTerm_restriction (q : Sections) (z : J → Circle) :
    rationalOrbitCompactPositiveConstantTerm hG hi hν I hKc hPK π C hC mu hsq I' hA
      hζ hB hmem z (restriction q z) =
      rationalOrbitPositiveConstantTerm hG hi hν I hKc hPK π C hC mu hsq I' hA q (omega z) := by
  exact congrArg (positivePart (standardComponentHom hA))
    (rationalOrbitCompactConstantTerm_restriction hG hi hν I hKc hPK π C hC mu hsq I' hA
      hζ hB hmem q z)

end Langlands.HarishChandraSchwartz
