import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalLeviXiComparison
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviOriginalOrbitXiBound

/-! # Original-orbit constant-term polynomial growth from the uniform threshold -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

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

set_option hygiene false in
local notation "𝐌" => standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] (mu : Measure (𝐌 ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)
  (J : Finset (RationalPointFamily.SimpleRoot i ν))
  {q : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν (RationalPointFamily.rootSet i ν J) A q)
  (hM' : IsIwasawaPair
    ((standardParabolicPoints i ν ∅).subgroupOf
      (standardLeviPoints i ν (RationalPointFamily.rootSet i ν J)))
    ((K : Subgroup (rationalPoints G)).subgroupOf
      (standardLeviPoints i ν (RationalPointFamily.rootSet i ν J))))

/-- Every original smooth orbit section has the full shifted-chamber polynomial estimate
for its actual full constant term, at the supplied matrix height. -/
def HasRationalOrbitConstantTermPolynomialBounds
    {n : ℕ} [Nonempty (Fin n)] (ρ : MatrixRepresentation G (Fin n)) : Prop :=
  ∀ Φ : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π,
    HasRationalConstantTermPolynomialBound hG hi hν hKc hM' ρ
      (rationalOrbitConstantTerm hG hi hν I hKc hPK π C hC mu hsq J hA Φ)

variable [BorelSpace (𝐌 ⧸ C)]

/-- The original global orbit coefficient bound, exact full-chamber threshold and full-M0
Xi comparison give polynomial growth of the actual constant term. The upper Xi statement
and exact threshold remain explicit intermediate obligations. -/
theorem hasRationalOrbitConstantTermPolynomialBounds_of_threshold
    (hupper : RationalXiUpperBoundStatement.{u})
    (hthreshold : RationalOrbitConstantTermThresholdStatement
      hG hi hν I hKc hPK π C hC mu hsq J hA)
    {ζ : cocharacterLattice S}
    (hζ : IsStandardCocharacter i ν (RationalPointFamily.rootSet i ν J) ζ)
    {K0 : Subgroup (rationalPoints G)} {B : Set (Subgroup (rationalPoints G))}
    (hK0o : IsOpen (K0 : Set (rationalPoints G)))
    (hK0c : IsCompact (K0 : Set (rationalPoints G)))
    (hB : CompactOpenNormalBasis K0 B)
    (hmem : ∀ L ∈ B, StandardParabolicBasisMember i ν (RationalPointFamily.rootSet i ν J) q L)
    (hbasis : SimultaneousStandardBasisAt i ν K0)
    (hcartan : RationalPointFamily.FiniteCartanCovering F i ν K0)
    (hcovers : ∀ R ⊆ simpleRelativeRoots i ν, StandardLeviCartanCovering F i ν R K0)
    {n : ℕ} [Nonempty (Fin n)] (ρ : MatrixRepresentation G (Fin n))
    (hρ : IsClosedSubgroup ρ) :
    HasRationalOrbitConstantTermPolynomialBounds hG hi hν I hKc hPK π C hC mu hsq J hA hM' ρ := by
  intro Φ
  have hcomparison := hasRationalXiLeviComparison_of_upperBound hG hi hν
    (RationalPointFamily.rootSet_subset i ν J) K.isOpen hKc hM' hupper hK0c hbasis
    (hcovers ∅ (Set.empty_subset _)) hPK ρ hρ
  obtain ⟨t, ht, hth⟩ := hthreshold hζ hK0o hK0c hB hmem hbasis hcartan hcovers Φ
  exact hasRationalConstantTermPolynomialBound_of_threshold hG hi hν hKc hPK hM' ρ
    hcomparison ⟨t, ht.le, hth⟩
    (exists_norm_rationalInducedOrbitCoefficientMap_le_rationalXi_of_squareIntegrable
      hG hi hν I hKc hPK hK0c hbasis
      (hcovers _ (RationalPointFamily.rootSet_subset i ν I)) π C hC mu hsq Φ)

end Langlands.HarishChandraSchwartz
