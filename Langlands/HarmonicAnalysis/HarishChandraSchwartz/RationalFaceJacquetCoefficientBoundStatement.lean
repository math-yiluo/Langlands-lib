import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalFaceLattice

/-! # Facewise Jacquet coefficient growth on actual rational points -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

/-- Uniform polynomial growth on each translated central face lattice, assuming
uniform unipotence of the normalized Jacquet action on that lattice. -/
def RationalFaceJacquetCoefficientBoundStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (S : CommGroupScheme (Spec (CommRingCat.of F)))
    (V : Type uV) [AddCommGroup V] [Module ℂ V],
  ∀ (hG : IsConnectedReductive G)
    {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
    {ν : cocharacterLattice S} (hν : IsGenericCocharacter i ν)
    {J : Set (characterLattice S)} (hJ : J ⊆ simpleRelativeRoots i ν)
    (hexists : ∃ ζ, IsStandardCocharacter i ν J ζ)
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (ρ : MatrixRepresentation G n) (hρ : IsClosedSubgroup ρ)
    (π : Representation ℂ (rationalPoints G) V) (r : ℕ)
    (hr : ∀ x : Multiplicative (faceCocharacterLattice J),
      (Jacquet.normalizedActionOfModulus π
        (standardUnipotentPoints i ν J) (standardLeviPoints i ν J)
        (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J)
        (standardUnipotentModulus i ν J) (faceUniformizerPowers i ν J x) - 1) ^ r = 0),
    ∃ d : ℕ, ∀ (v : V)
      (ell : Module.Dual ℂ (Jacquet.Coinvariants π (standardUnipotentPoints i ν J)))
      (m : cocharacterLattice S),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x : faceCocharacterLattice J,
        ‖ell (Jacquet.mk π (standardUnipotentPoints i ν J)
          (π (Aubert.General.uniformizerPowers i (.ofAdd ((x : cocharacterLattice S) + m))) v))‖ ≤
          C * (NNReal.sqrt (rationalMinimalModulus i ν
              (uniformizerPowersParabolic i ν (.ofAdd ((x : cocharacterLattice S) + m))) :
                ℝ≥0) : ℝ) *
            (1 + rationalHeight (F := F) ρ
              (Aubert.General.uniformizerPowers i (.ofAdd ((x : cocharacterLattice S) + m)))) ^ d

end Langlands.HarishChandraSchwartz
