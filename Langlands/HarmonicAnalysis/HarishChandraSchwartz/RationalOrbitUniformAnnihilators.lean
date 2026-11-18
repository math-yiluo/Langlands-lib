import Langlands.Representation.Jacquet.StandardUnitaryJacquetFixedLevel
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitConstantTermInvariance

/-! # Uniform annihilators of the original orbit constant terms -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.Plancherel

universe uG uV uI

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  {M : Subgroup G} {Ix : Type uI} (ν : Ix → (M →* ℝ≥0ˣ))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))

/-- The original inducing object twisted by the specified unitary character,
with its actual membership in the full unitary orbit. -/
def unitaryOrbitTwistRepresentative (χ : unitaryUnramifiedCharacters ν) :
    UnitaryOrbitRepresentative ν π :=
  ⟨IrreducibleAdmissibleRep.twist (unitaryUnramifiedInclusion ν χ).val.toMonoidHom
    (unramifiedCharacter_isOpen_ker _ _) π, χ, rfl⟩

/-- These literal twists cover every original discrete-series orbit class. -/
theorem unitaryOrbitTwistRepresentative_surjective
    (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
    [MeasurableSpace (M ⧸ C)] (mu : Measure (M ⧸ C)) [mu.IsHaarMeasure]
    (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu) :
    Function.Surjective (fun χ => unitaryOrbitRepresentativeDiscreteSeriesOrbit ν π C hC mu hsq
      (unitaryOrbitTwistRepresentative ν π χ)) := by
  rintro ⟨ω, χ, hχ⟩
  exact ⟨χ, Subtype.ext hχ⟩

end Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
  (I : Finset (RationalPointFamily.SimpleRoot i ν))
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)

set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x}

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] (mu : Measure (𝐌 ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)
  (J : Finset (RationalPointFamily.SimpleRoot i ν))
  {A : CommGroupScheme (Spec (CommRingCat.of F))} {q : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν (RationalPointFamily.rootSet i ν J) A q)

set_option hygiene false in
local notation "𝒪" => discreteSeriesOrbit C hC mu
  (RationalPointFamily.leviRationalNormCharacters i ν I) (discreteSeriesClass C hC mu π hsq)

/-- The remaining spectral contraction property for the original actual
standard unitary induced family, at the specified unchanged component point. -/
def HasStandardUnitaryJacquetContraction (a : rationalPoints A.toGrp) : Prop :=
  ∀ ψ : unramifiedCharacters (RationalPointFamily.leviRationalNormCharacters i ν I),
    (∀ m, ‖(ψ.val m : ℂ)‖ = 1) → ∀ χ : rationalPoints A.toGrp →* ℂˣ,
      IsGeneralizedEigencharacter
        (((standardOrdinaryJacquetObject (i := i) (ν := ν)
          (J := RationalPointFamily.rootSet i ν J)
          (standardUnramifiedInducedObject hG hi hν I π.obj ψ)).representation).comp
            (standardComponentHom hA)) χ →
        (¬ ∀ b, ‖(χ b : ℂ)‖ = 1) → ‖(χ a : ℂ)‖ < 1

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
/-- Strict nonunitary contraction in the original induced Jacquet family
implies uniform split annihilators for the original chosen orbit constant terms.
The full orbit, its arbitrary coherent section, the common standard level and
all fixed polynomial degrees are retained or derived. -/
theorem hasUniformSplitAnnihilators_rationalOrbitConstantTerm_of_contraction
    {ζ : cocharacterLattice S}
    (hζ : IsStandardCocharacter i ν (RationalPointFamily.rootSet i ν J) ζ)
    {K0 : Subgroup (rationalPoints G)} {B : Set (Subgroup (rationalPoints G))}
    (hB : CompactOpenNormalBasis K0 B)
    (hmem : ∀ L ∈ B, StandardParabolicBasisMember i ν (RationalPointFamily.rootSet i ν J) q L)
    (a : rationalPoints A.toGrp)
    (hcontract : HasStandardUnitaryJacquetContraction hG hi hν I π J hA a)
    (Φ : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π) :
    HasUniformSplitAnnihilators (standardComponentHom hA) a
      (rationalOrbitConstantTerm hG hi hν I hKc hPK π C hC mu hsq J hA Φ) := by
  classical
  let νM := RationalPointFamily.leviRationalNormCharacters i ν I
  choose χ hχ using fun ω : 𝒪 =>
    unitaryOrbitTwistRepresentative_surjective νM π C hC mu hsq ω
  let ψ := fun ω => unitaryUnramifiedInclusion νM (χ ω)
  have hψ : ∀ ω m, ‖((ψ ω).val m : ℂ)‖ = 1 := fun ω => (χ ω).property.2
  let R := fun ω => unitaryOrbitTwistRepresentative νM π (χ ω)
  have hrep (ω : 𝒪) : unitaryOrbitRepresentativeDiscreteSeriesOrbit νM π C hC mu hsq (R ω) = ω :=
    hχ ω
  have hf (ω : 𝒪) :
      rationalInducedOrbitCoefficientMap hG hi hν I hKc hPK π C hC mu hsq Φ ω =
        rationalInducedCoefficientMap hG hi hν I hKc hPK
          (R ω).val.obj (R ω).val.property.2 (Φ.val (R ω)) := by
    have hh := rationalInducedOrbitCoefficientMap_representative
      hG hi hν I hKc hPK π C hC mu hsq Φ (R ω)
    rw [hrep ω] at hh
    exact hh
  have ht : ∀ ω : 𝒪,
      ∃ t : CoefficientTensor (standardUnramifiedInducedObject hG hi hν I π.obj (ψ ω)),
        coefficientTensorMap (standardUnramifiedInducedObject hG hi hν I π.obj (ψ ω)) t =
          rationalInducedOrbitCoefficientMap hG hi hν I hKc hPK π C hC mu hsq Φ ω := by
    intro ω
    have hrange :
        rationalInducedCoefficientMap hG hi hν I hKc hPK
            (R ω).val.obj (R ω).val.property.2 (Φ.val (R ω)) ∈
          LinearMap.range (normalizedCoefficientMap
            (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
            (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
            (R ω).val.obj) := by
      rw [← range_rationalInducedCoefficientMap hG hi hν I hKc hPK
        (R ω).val.obj (R ω).val.property.2]
      exact LinearMap.mem_range_self _ _
    obtain ⟨t, ht⟩ := hrange
    exact ⟨t, ht.trans (hf ω).symm⟩
  choose t ht using ht
  have hCT (ω : 𝒪) :
      standardConstantTerm hA
          (fun g => coefficientTensorMap (standardUnramifiedInducedObject hG hi hν I π.obj (ψ ω))
            (t ω) g) =
        rationalOrbitConstantTerm hG hi hν I hKc hPK π C hC mu hsq J hA Φ ω := by
    rw [ht ω]
    rfl
  obtain ⟨H, _, hHc, hfix⟩ :=
    rationalInducedOrbitCoefficientMap_hasUniformBiInvariance hG hi hν I hKc hPK π C hC mu hsq Φ
  obtain ⟨L, hLB, hLH⟩ := hB.2.mem_iff.mp H.mem_nhds_one
  let Lop := basisOpenSubgroup hB hLB
  have hLc : IsCompact (Lop : Set (rationalPoints G)) := (hB.1 L hLB).2.2.2
  have hinv : ∀ (ω : 𝒪)
      (k : Lop.comap (standardLeviPoints i ν (RationalPointFamily.rootSet i ν J)).subtype
        continuous_subtype_val) (m : standardLeviPoints i ν (RationalPointFamily.rootSet i ν J)),
      standardConstantTerm hA
          (fun g => coefficientTensorMap (standardUnramifiedInducedObject hG hi hν I π.obj (ψ ω))
            (t ω) g) (m * k) =
        standardConstantTerm hA
          (fun g => coefficientTensorMap (standardUnramifiedInducedObject hG hi hν I π.obj (ψ ω))
            (t ω) g) m := by
    intro ω k m
    rw [hCT ω]
    unfold rationalOrbitConstantTerm
    apply standardConstantTerm_mul_right_eq_of_invariance hA hi hζ hHc
    · intro g k hk
      simpa only [OneMemClass.coe_one, one_mul] using hfix ω (1 : H) ⟨k, hk⟩ g
    · exact hLH k.property
  have hann := hasUniformSplitAnnihilators_standardUnramifiedConstantTerms
    hG hi hν I hKc hPK J hA π.obj π.property.1 π.property.2 Lop hLc (hmem L hLB)
    hB hmem ψ hψ t a hinv (fun ω χ hgen hχU => hcontract (ψ ω) (hψ ω) χ hgen hχU)
  simpa only [hCT] using hann

end Langlands.HarishChandraSchwartz
