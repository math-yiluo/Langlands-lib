import Langlands.BruhatTits.Cartan.ParahoricDominantQuotient
import Langlands.BruhatTits.SpecialCompact.StandardBasisProperty
import Langlands.Geometry.Building.SpecialCompact
import Langlands.Representation.Plancherel.RenardRepresentativeData

/-! # Iwahori contraction when the split torus supplies the valuation image -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.BruhatTits.Cartan Langlands.BruhatTits.SpecialCompact
open Langlands.Plancherel.RenardCartan

namespace Langlands.Hecke

/-- For a generic cocharacter, when the maximal split torus supplies the whole
centralizer valuation image, the V.5.2 basis clauses for the minimal standard
parabolic extend to all dominant centralizer points. This supplies the two parts of (P) in
`IwahoriHeckeSubalgebraFinitenessStatement`. -/
def IwahoriDominantCentralizerContractionStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (B : ParahoricBuildingData G) (ν : cocharacterLattice B.S)
    (x : B.Apartment) (K : Subgroup (rationalPoints G)),
    IsGenericCocharacter B.i ν →
    B.apartment.specialCompactSubgroup x ≤ Subgroup.normalizer (K : Set (rationalPoints G)) →
    splitValuationImage B.centralizer.s = ⊤ →
    (∃ (A : CommGroupScheme (Spec (CommRingCat.of F))) (q : A.toGrp ⟶ B.S.toGrp),
      IsCompatibleStandardSplitComponent B.i ν ∅ A q ∧
        StandardParabolicBasisMember B.i ν ∅ q K) →
    let dominant := rationalPoints.map B.centralizer.j '' parahoricDominantSet B ν
    WeakChamberContraction K (standardUnipotentPoints B.i ν ∅)
      (standardOppositeUnipotentPoints B.i ν ∅) dominant ∧
    LeviIntersectionNormalization K (standardLeviPoints B.i ν ∅) dominant

end Langlands.Hecke
