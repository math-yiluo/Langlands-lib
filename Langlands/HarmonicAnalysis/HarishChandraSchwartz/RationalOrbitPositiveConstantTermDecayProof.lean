import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalInducedJacquetProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiUpperBoundReduction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitConstantTermThresholdProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitPositiveDecayReduction

/-! # Positive constant-term decay on the actual induced orbit -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open Langlands.BruhatTits.SpecialCompact

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
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (RationalPointFamily.SimpleRoot i ν))
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))

-- `M_I(F)` as a subtype of `G(F) = rationalPoints G`, with the membership of `Subgroup G(F)`.
set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x}

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] (mu : Measure (𝐌 ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)
  (I' : Finset (RationalPointFamily.SimpleRoot i ν))
  {A : CommGroupScheme (Spec (CommRingCat.of F))} {qA : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν (RationalPointFamily.rootSet i ν I') A qA)

/-- The actual positive constant term decays exponentially, uniformly over
the whole smooth unitary orbit section and the full closed decay region. -/
theorem rationalOrbitPositiveConstantTermDecay
    (hM' : IsIwasawaPair
      ((standardParabolicPoints i ν ∅).subgroupOf
        (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I')))
      ((K : Subgroup (rationalPoints G)).subgroupOf
        (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I')))) :
    RationalOrbitPositiveConstantTermDecayStatement
      hG hi hν I hKc hPK π C hC mu hsq I' hA hM' := by
  unfold RationalOrbitPositiveConstantTermDecayStatement
  intro hBorel ζ hζ K₀ B hK₀o hK₀c hBasis hMember hSimultaneous hCartan hCover N hN ψ
  have hupper : RationalXiUpperBoundStatement.{u} :=
    rationalXiUpperBound_of_jacquetUnipotent rationalMinimalInducedJacquetUnipotent
  exact rationalOrbitPositiveDecay_of_xiUpperBound_and_threshold
    hG hi hν I hKc hPK π C hC mu hsq I' hA hM' hupper
    (rationalOrbitConstantTermThreshold hG hi hν I hKc hPK π C hC mu hsq I' hA)
    hζ hK₀o hK₀c hBasis hMember hSimultaneous hCartan hCover N hN ψ

end Langlands.HarishChandraSchwartz
