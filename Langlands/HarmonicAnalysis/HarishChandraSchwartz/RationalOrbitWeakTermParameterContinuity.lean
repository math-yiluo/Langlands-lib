import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitConstantTermRayContinuity
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.WeakProjectionTailContinuity
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitJacquetContraction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiUpperBoundReduction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalInducedJacquetProof

/-! # Parameter continuity of actual weak constant terms -/

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
local notation "weakTerm" => rationalOrbitWeakConstantTerm hG hi hν I hKc hPK π C hC mu hsq J hA

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
/-- The actual weak constant terms of an original smooth orbit section are continuous in the
whole unitary orbit at every lower-Levi point, on the supplied standard basis and Cartan data. -/
def RationalOrbitWeakTermParameterContinuityStatement : Prop :=
  ∀ [BorelSpace (M₁ ⧸ C)],
  ∀ {K0 : Subgroup (rationalPoints G)} {B : Set (Subgroup (rationalPoints G))},
    IsCompact (K0 : Set (rationalPoints G)) →
    SimultaneousStandardBasisAt i ν K0 →
    StandardLeviCartanCovering F i ν (RationalPointFamily.rootSet i ν I) K0 →
    CompactOpenNormalBasis K0 B →
    (∀ L ∈ B, StandardParabolicBasisMember i ν (RationalPointFamily.rootSet i ν J) q L) →
    ∀ (Φ : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π) (m : M₂),
      Continuous (fun ω : 𝒪 => weakTerm Φ ω m)

include hζ in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
/-- Use the uniform gap for split annihilators at the chosen strict ray and the continuous
full constant-term samples on its tail. -/
theorem rationalOrbitWeakTermParameterContinuity :
    RationalOrbitWeakTermParameterContinuityStatement hG hi hν I J hKc hPK π C hC mu hsq hA := by
  intro _ K0 B hK0c hbasis hcover hB hmem Φ m
  let aM := (hA.centralStrictElement i ν hi hζ : M₂)
  obtain ⟨a, ha, hea⟩ := (hA.strictElement_spec i ν hi hζ).2.2.2
  have haM : standardComponentHom hA a = aM := Subtype.ext hea
  obtain ⟨N, hN⟩ := rationalOrbitConstantTermRayContinuity hG hi hν I J hKc hPK
    π C hC mu hsq hA hζ hB hmem Φ m
  have hupper := rationalXiUpperBound_of_jacquetUnipotent rationalMinimalInducedJacquetUnipotent
  have hann := hasUniformSplitAnnihilators_rationalOrbitConstantTerm_of_xiUpperBound
    hG hi hν I hKc hPK hK0c hbasis hcover π C hC mu hsq J hA hB hmem hupper hζ a ha Φ
  exact hann.continuous_weakPart_of_tail m N (fun n hn => by
    rw [haM]
    exact hN n hn)

end Langlands.HarishChandraSchwartz
