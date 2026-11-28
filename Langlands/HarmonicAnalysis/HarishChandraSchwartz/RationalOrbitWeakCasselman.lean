import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitUniformAnnihilators
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakCasselmanCoefficient

/-! # The Casselman pairing for weak orbit coefficients -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.BruhatTits.SpecialCompact
open Langlands.Jacquet

namespace Langlands.HarishChandraSchwartz

universe u uV

set_option maxRecDepth 8000

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (RationalPointFamily.SimpleRoot i ν))
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)

open RationalPointFamily

set_option hygiene false in
local notation "𝐌" => standardLeviPoints i ν (rootSet i ν I)
set_option hygiene false in
local notation "decomp" => isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I)
set_option hygiene false in
local notation "closedU" => isClosed_standardUnipotentPoints i ν (rootSet i ν I)
set_option hygiene false in
local notation "νM" => leviRationalNormCharacters i ν I

/-- Specialize compact coefficient duality to the actual standard induction and the Haar
probability of `K`. -/
def rationalInducedCoefficientTensorEquiv (τ : SmoothRep.{0, u, uV} ℂ 𝐌)
    (hτ : τ.IsAdmissible) :
    Representation.Equiv (productInducedCoefficientObject decomp closedU τ).representation
      (coefficientTensorAction ((normalizedInductionFunctor decomp closedU).obj τ)) :=
  haveI := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  CompactInduction.coefficientTensorEquiv decomp closedU τ K hKc
    (isClosed_standardParabolicPoints_rootSet hG hi hν I)
    (continuous_projection_standard hG hi hν (rootSet_subset i ν I) decomp)
    (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
    (fun g => rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl (rootSet_subset i ν I)) hτ

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] (mu : Measure (𝐌 ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)

set_option hygiene false in
local notation "twistRep" χ => unitaryOrbitTwistRepresentative νM π χ
set_option hygiene false in
local notation "induced" χ =>
  (normalizedInductionFunctor decomp closedU).obj (twistRep χ).val.obj
set_option hygiene false in
local notation "orbitMap" =>
  discreteSeriesOrbitMap C hC mu νM (discreteSeriesClass C hC mu π hsq)
set_option hygiene false in
local notation "Sections" => rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π

/-- The coefficient tensor of the value of an orbit section at a specified unitary twist. -/
def rationalOrbitCoefficientTensor (Φ : Sections) (χ : unitaryUnramifiedCharacters νM) :
    CoefficientTensor (induced χ) :=
  rationalInducedCoefficientTensorEquiv hG hi hν I hKc hPK
    (twistRep χ).val.obj (twistRep χ).val.property.2 (Φ.val (twistRep χ))

set_option maxHeartbeats 1600000 in
/-- Compact duality sends the section value to a tensor giving the actual orbit coefficient. -/
theorem coefficientTensorMap_rationalOrbitCoefficientTensor (Φ : Sections)
    (χ : unitaryUnramifiedCharacters νM) :
    coefficientTensorMap (induced χ) (rationalOrbitCoefficientTensor hG hi hν I hKc hPK π Φ χ) =
      rationalInducedOrbitCoefficientMap hG hi hν I hKc hPK π C hC mu hsq Φ (orbitMap χ) := by
  have horbit :
      unitaryOrbitRepresentativeDiscreteSeriesOrbit νM π C hC mu hsq (twistRep χ) =
        orbitMap χ :=
    Subtype.ext (Subtype.ext rfl)
  have hcoef :
      coefficientTensorMap (induced χ) (rationalOrbitCoefficientTensor hG hi hν I hKc hPK π Φ χ) =
        rationalInducedCoefficientMap hG hi hν I hKc hPK (twistRep χ).val.obj
          (twistRep χ).val.property.2 (Φ.val (twistRep χ)) := by
    simp only [rationalInducedCoefficientMap_eq_coefficientMap, CompactInduction.coefficientMap,
      LinearMap.comp_apply, normalizedCoefficientMap, rationalOrbitCoefficientTensor,
      rationalInducedCoefficientTensorEquiv, Representation.IntertwiningMap.toLinearMap_apply]
    rfl
  exact hcoef.trans ((rationalInducedOrbitCoefficientMap_representative
    hG hi hν I hKc hPK π C hC mu hsq Φ (twistRep χ)).symm.trans
      (congrArg (rationalInducedOrbitCoefficientMap hG hi hν I hKc hPK π C hC mu hsq Φ) horbit))

include hKc hPK in
private theorem induced_isAdmissible (χ : unitaryUnramifiedCharacters νM) :
    (induced χ).IsAdmissible :=
  CompactInduction.induced_isAdmissible decomp closedU K hKc
    (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK) (twistRep χ).val.obj
    (continuous_projection_standard hG hi hν (rootSet_subset i ν I) decomp)
    (twistRep χ).val.property.2

variable (I' : Finset (SimpleRoot i ν)) {ζ' : cocharacterLattice S}
  (hζ' : IsStandardCocharacter i ν (rootSet i ν I') ζ')
  {K₀ : Subgroup (rationalPoints G)} {B : Set (Subgroup (rationalPoints G))}
  (hB : CompactOpenNormalBasis K₀ B) {qA : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν (rootSet i ν I') A qA)
  (hmem : ∀ L ∈ B, StandardParabolicBasisMember i ν (rootSet i ν I') qA L)

set_option maxHeartbeats 1600000 in
/-- The weak constant term of an orbit coefficient is the coefficient of its two unitary
normalized Jacquet classes in the Casselman pairing. -/
def RationalOrbitWeakCasselmanStatement : Prop :=
  ∀ (χ : unitaryUnramifiedCharacters νM) (Φ : Sections),
    let D := standardCasselmanPairingData hG hi hν hζ' hB hA hmem
    letI : WeaklyLocallyCompactSpace D.M := by
      change WeaklyLocallyCompactSpace (standardLeviPoints i ν (rootSet i ν I'))
      let : LocallyCompactSpace (standardLeviPoints i ν (rootSet i ν I')) :=
        (isClosed_standardLeviPoints i ν (rootSet i ν I')).locallyCompactSpace
      infer_instance
    let ρ := induced χ
    let hρ := induced_isAdmissible hG hi hν I hKc hPK π χ
    let hadm := standardCasselmanPairingData_normalizedActions_isAdmissible
      hG hi hν hζ' hB hA hmem ρ hρ
    let hj (a : rationalPoints A.toGrp) : standardComponentHom hA a ∈ Subgroup.center D.M :=
      Subgroup.mem_center_iff.mpr fun m => (standardComponentHom_commute hA a m).symm
    ∀ (b : Coinvariants (smoothContragredient ρ.representation) D.N →ₗ[ℂ]
          Coinvariants ρ.representation D.Nbar →ₗ[ℂ] ℂ),
      D.IsStablePairing ρ.representation ρ.isSmooth b →
        rationalOrbitWeakConstantTerm hG hi hν I hKc hPK π C hC mu hsq I' hA Φ (orbitMap χ) =
          StablePairingData.unitaryCoefficientTensorConstantTerm (D := D)
            (ρ := ρ.representation) (standardRadicalModulus i ν (rootSet i ν I'))
            (standardComponentHom hA) hj hadm.1 hadm.2 b
            (rationalOrbitCoefficientTensor hG hi hν I hKc hPK π Φ χ)

set_option maxHeartbeats 1800000 in
/-- Apply the weak tensor formula to the actual tensor supplied by compact duality. -/
theorem rationalOrbitWeakCasselman :
    RationalOrbitWeakCasselmanStatement hG hi hν I hKc hPK π C hC mu hsq I' hζ' hB hA hmem := by
  intro χ Φ D ρ hρ hadm hj b hb
  have hcoeff := coefficientTensorMap_rationalOrbitCoefficientTensor
    hG hi hν I hKc hPK π C hC mu hsq Φ χ
  have hformula := standardWeakTensorCasselman hG hi hν hζ' hB hA hmem
    ρ hρ b hb
    (rationalOrbitCoefficientTensor hG hi hν I hKc hPK π Φ χ)
  exact (congrArg (fun f : LocallyConstant (rationalPoints G) ℂ =>
    weakPart (standardComponentHom hA) (standardConstantTerm hA fun g => f g))
    hcoeff).symm.trans hformula

end Langlands.HarishChandraSchwartz
