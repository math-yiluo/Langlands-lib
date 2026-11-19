import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeights
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OppositeUnipotentDisplacement
import Langlands.Representation.Aubert.General.RationalOppositeParabolic

/-! # Power contraction of the inverse minimal weight on the actual opposite radical -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact

/-- The power estimate used in Waldspurger II.4.1 (1) for the actual minimal weight. -/
def RationalOppositeWeightContractionStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i → ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν →
    ∀ (ζ : cocharacterLattice S) (K : Subgroup (rationalPoints G))
      (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K),
      IsCompact (K : Set (rationalPoints G)) →
    ∀ (t : Fˣ), LocalField.residueNormalizedAbsoluteValue F (t : F) < 1 →
    let a : rationalPoints G := gmRationalPoint t ≫ (CommGroupScheme.groupHom ζ ≫ i).hom.hom
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (x : Aubert.General.RationalPointFamily.oppositeUnipotent i ζ),
      (iwasawaWeight hPK (rationalMinimalModulus i ν)
        ((a ^ m)⁻¹ * (x : rationalPoints G) * a ^ m))⁻¹ ≤
        C * (1 + (Real.sqrt (LocalField.residueNormalizedAbsoluteValue F (t : F))) ^ m *
          (iwasawaWeight hPK (rationalMinimalModulus i ν) (x : rationalPoints G))⁻¹)

end Langlands.HarishChandraSchwartz
