import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitUniformAnnihilators
import Langlands.Representation.Jacquet.StandardInducedTranslatedRay

/-! # Parameter continuity on tails of actual constant-term rays -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

universe u uV

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
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
  (I J : Finset (RationalPointFamily.SimpleRoot i ν))
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)

set_option hygiene false in
local notation "M₁" => standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)
set_option hygiene false in
local notation "M₂" => standardLeviPoints i ν (RationalPointFamily.rootSet i ν J)

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := M₁))
  (C : Subgroup M₁) [C.Normal] (hC : C ≤ Subgroup.center M₁)
  [MeasurableSpace (M₁ ⧸ C)] (mu : Measure (M₁ ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)
  {q : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν (RationalPointFamily.rootSet i ν J) A q)
  {ζ : cocharacterLattice S} (hζ : IsStandardCocharacter i ν (RationalPointFamily.rootSet i ν J) ζ)

set_option hygiene false in
local notation "νM" => RationalPointFamily.leviRationalNormCharacters i ν I
set_option hygiene false in
local notation "𝒪" => discreteSeriesOrbit C hC mu νM (discreteSeriesClass C hC mu π hsq)
set_option hygiene false in
local notation "coeff" => rationalInducedOrbitCoefficientMap hG hi hν I hKc hPK π C hC mu hsq
set_option hygiene false in
local notation "fullTerm" => rationalOrbitConstantTerm hG hi hν I hKc hPK π C hC mu hsq J hA
set_option hygiene false in
local notation "aM" => (hA.centralStrictElement i ν hi hζ : M₂)

set_option maxHeartbeats 1000000 in
/-- At every fixed lower-Levi point all sufficiently deep translates along the chosen strict
ray give continuous values of the full constant term in the entire actual orbit. -/
def RationalOrbitConstantTermRayContinuityStatement : Prop :=
  ∀ {K0 : Subgroup (rationalPoints G)} {B : Set (Subgroup (rationalPoints G))},
    CompactOpenNormalBasis K0 B →
    (∀ L ∈ B, StandardParabolicBasisMember i ν (RationalPointFamily.rootSet i ν J) q L) →
    ∀ (Φ : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π) (m : M₂),
      ∃ N : ℕ, ∀ n, N ≤ n → Continuous (fun ω : 𝒪 => fullTerm Φ ω (m * aM ^ n))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
/-- Use a common bi-invariance level after the fixed Levi translation and the uniform
induced fixed-space dimension. The exact half-modulus relates the tail to the orbit coefficient. -/
theorem rationalOrbitConstantTermRayContinuity :
    RationalOrbitConstantTermRayContinuityStatement hG hi hν I J hKc hPK π C hC mu hsq hA hζ := by
  intro K0 B hB hmem Φ m
  obtain ⟨H, -, -, hfix⟩ := rationalInducedOrbitCoefficientMap_hasUniformBiInvariance
    hG hi hν I hKc hPK π C hC mu hsq Φ
  let Hm := H ⊓ Jacquet.conjOpenSubgroup (m : rationalPoints G)⁻¹ H
  obtain ⟨L, hLB, hLHm⟩ := hB.2.mem_iff.mp Hm.mem_nhds_one
  let Lop := basisOpenSubgroup hB hLB
  let N := standardInducedFixedOrder hG hi hν I π.obj Lop
  have hformula (n : ℕ) (hn : N ≤ n) (ω : 𝒪) :
      coeff Φ ω (m * aM ^ n : M₂) =
        standardHalfModulus i ν (RationalPointFamily.rootSet i ν J) (m * aM ^ n) *
          fullTerm Φ ω (m * aM ^ n) := by
    obtain ⟨χ, hω⟩ := unitaryOrbitTwistRepresentative_surjective νM π C hC mu hsq ω
    let ψ := unitaryUnramifiedInclusion νM χ
    let R := unitaryOrbitTwistRepresentative νM π χ
    have hf := rationalInducedOrbitCoefficientMap_representative
      hG hi hν I hKc hPK π C hC mu hsq Φ R
    rw [show unitaryOrbitRepresentativeDiscreteSeriesOrbit νM π C hC mu hsq R = ω from hω] at hf
    have hrange :
        rationalInducedCoefficientMap hG hi hν I hKc hPK R.val.obj R.val.property.2 (Φ.val R) ∈
          LinearMap.range (normalizedCoefficientMap
            (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
            (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) R.val.obj) := by
      rw [← range_rationalInducedCoefficientMap hG hi hν I hKc hPK R.val.obj R.val.property.2]
      exact LinearMap.mem_range_self _ _
    obtain ⟨t, ht⟩ := hrange
    have hcoeff :
        coefficientTensorMap (standardUnramifiedInducedObject hG hi hν I π.obj ψ) t = coeff Φ ω :=
      ht.trans hf.symm
    have hinv : ∀ (k l : H) g,
        coefficientTensorMap (standardUnramifiedInducedObject hG hi hν I π.obj ψ) t
          ((k : rationalPoints G) * g * (l : rationalPoints G)) =
        coefficientTensorMap (standardUnramifiedInducedObject hG hi hν I π.obj ψ) t g := by
      intro k l g
      rw [hcoeff]
      exact hfix ω k l g
    have heq := standardUnramifiedConstantTerm_mul_ray_threshold hG hi hν I J hKc hPK
      hA hζ hB hmem π.obj π.property.2 hLB ψ t m
      (biInvariant_mul_left_of_le_conj hinv (m : rationalPoints G)
        (fun _ hz => (hLHm hz).1) (fun _ hz => (hLHm hz).2)) hn
    simpa only [HasStandardConstantTermEqualityAt, hcoeff, rationalOrbitConstantTerm] using heq
  refine ⟨N, fun n hn => ?_⟩
  let x : M₂ := m * aM ^ n
  let δ := standardHalfModulus i ν (RationalPointFamily.rootSet i ν J) x
  have hδ : δ ≠ 0 := standardHalfModulus_ne_zero x
  have h : (fun ω : 𝒪 => fullTerm Φ ω x) = fun ω : 𝒪 => δ⁻¹ * coeff Φ ω x := by
    funext ω
    rw [hformula n hn ω, ← mul_assoc, inv_mul_cancel₀ hδ, one_mul]
  change Continuous (fun ω : 𝒪 => fullTerm Φ ω x)
  rw [h]
  exact continuous_const.mul (continuous_rationalInducedOrbitCoefficientMap
    hG hi hν I hKc hPK π C hC mu hsq Φ x)

end Langlands.HarishChandraSchwartz
