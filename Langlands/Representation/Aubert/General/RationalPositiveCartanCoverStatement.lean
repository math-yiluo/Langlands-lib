import Langlands.Representation.Aubert.General.RationalCuspidalCompactRestrictionStatement
import Langlands.Representation.Plancherel.RenardSpecialCompactComparison

/-! # The finite Cartan cover needed by rational cuspidal compactness -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.BruhatTits.Cartan
open Langlands.Plancherel.RenardCartan

namespace Langlands.Aubert.General.RationalPointFamily

/-- The supplied comparison for one geometric special compact subgroup gives
the finite positive Cartan covering for that very same subgroup. -/
def RationalPositiveCartanCoverStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G)
    [Mono i.hom.hom.left] (ν : cocharacterLattice S)
    (D : KPApartmentData i (localFieldOrder F)) (x : D.Apartment)
    (Z : GroupScheme (Spec (CommRingCat.of F))) (j : Z ⟶ G)
    (s : S.toGrp ⟶ Z) (h : Function.Bijective (restrictionEvaluation s)),
    (torusCentralizer i).IsRepresentedBy j →
    s ≫ j = i →
    SpecialCompactRenardComparison D x ν j s h →
    FiniteCartanCovering F i ν (D.specialCompactSubgroup x)

end Langlands.Aubert.General.RationalPointFamily
