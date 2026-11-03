import Langlands.BruhatTits.SpecialCompact.StandardBasisProperty
import Langlands.Representation.Jacquet.IwahoriContraction

/-! # The actual-standard-group adapter to the Jacquet contraction input -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.BruhatTits.SpecialCompact

/-- The simultaneous actual-standard-group property supplies the existing
Jacquet input, including the existence of a contracting element and cofinality
for every open subgroup of the actual Levi. This is a target, not a proof of
the simultaneous property or of the adapter. -/
def SimultaneousBasisJacquetAdapterStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : S.toGrp ⟶ G) (_hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    ∀ (ν : cocharacterLattice S), IsGenericCocharacter i ν →
      ∀ K0 : Subgroup (rationalPoints G),
        SimultaneousStandardBasisAt i ν K0 →
          ∀ J : Set (characterLattice S), J ⊆ simpleRelativeRoots i ν →
            letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
            letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
            Langlands.Jacquet.HasIwahoriContractionBasis
              (standardUnipotentPoints i ν J)
              (standardLeviPoints i ν J)
              (standardOppositeUnipotentPoints i ν J)

end Langlands.BruhatTits.SpecialCompact
