import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RankZeroPacketStructure
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalRankZero
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardFourierTransform
import Langlands.Representation.Unitary.SmoothCoefficientBoundednessProof

/-! # Analytic inputs to the actual rank-zero Fourier family -/

noncomputable section

universe u uV

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.RationalSemistandard

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))

/-- At relative semisimple rank zero, the square weight used on the ambient
group is integrable, and actual normalized inductions of square-integrable
representations have tempered coefficients. -/
def RankZeroFourierBoundsStatement : Prop :=
  IsConnectedReductive G → IsMaximalSplitTorus i → IsGenericCocharacter i ν →
  relativeRootRank i = 0 →
    (IsClosedSubgroup ρ → ∀ (muG : Measure (rationalPoints G)) [muG.IsHaarMeasure],
      SquareIntegrableWeight muG (rationalXi hKc hPK) (rationalHeight (F := F) ρ)) ∧
    (∀ (p : SemistandardSpectralIndex i) (_d : CompactData p),
      ModularNormalization p →
      ∀ (C : Subgroup (levi p)) [C.Normal] (hC : C ≤ Subgroup.center (levi p))
        [MeasurableSpace (levi p ⧸ C)] [BorelSpace (levi p ⧸ C)]
        (muM : Measure (levi p ⧸ C)) [muM.IsHaarMeasure] [muM.IsInvInvariant]
        (A : SmoothRep.{0, u, uV} ℂ (levi p)),
        IsSquareIntegrableModCentralSubgroup C hC A.representation muM →
        HasTemperedCoefficients (rationalXi hKc hPK) (rationalHeight (F := F) ρ)
          ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj
            A).representation)

/-- In the trivial root system, `Ξ = 1`. Compactness of the norm kernel
gives the square estimate, and unitarizability gives tempered growth
with exponent zero. -/
theorem rankZeroFourierBounds :
    RankZeroFourierBoundsStatement.{u, uV} hKc hPK ρ := by
  intro hG hi hν hzero
  have hroots := simpleRelativeRoots_eq_empty_of_relativeRoots_eq_empty i ν
    (RankZero.relativeRoots_eq_empty_of_rankZero hG hi hzero)
  have hXi := rationalXi_eq_one_of_simpleRoots_empty hG hi hν hroots hKc hPK
  constructor
  · intro hρ muG _
    apply rationalSquareIntegrableWeight_of_compact_normKernel hG
      (isCompact_rationalCommonNormKernel_of_simpleRoots_empty hG hi hν hroots)
      ρ hρ muG (A := 1)
    intro g
    rw [hXi g, abs_one]
  · intro p d hdelta C _ hC _ _ muM _ _ A hsq
    let : LocallyCompactSpace (parabolic p) := (isClosed_parabolic p).locallyCompactSpace
    obtain ⟨b⟩ := isUnitarizable_of_isSquareIntegrableModCentralSubgroup C hC muM
      (compactOpenCofinal p d) hsq
    have hind : IsUnitarizable
        ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj
          A).representation :=
      ⟨CompactInduction.invariantPositiveForm (decomposition p) (isClosed_radical p)
        (isClosed_parabolic p) d.compact d.isCompact d.factorization_mem
        (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
        hdelta A b⟩
    let : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
    intro v ℓ
    obtain ⟨B, _, hB⟩ := hind.smoothCoefficient_bounded CompactOpenSubgroup.cofinal
      (rationalSemistandardFourierAdmissible p d A C hC muM hsq) ℓ v
    refine ⟨B, 0, fun g => ?_⟩
    rw [hXi g, Real.rpow_zero, mul_one, mul_one]
    exact hB g

end Langlands.HarishChandraSchwartz.RationalSemistandard
