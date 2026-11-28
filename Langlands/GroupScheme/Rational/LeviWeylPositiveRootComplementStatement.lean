import Langlands.GroupScheme.Rational.ClosedRootSubsetStatements

/-! # Levi Weyl action on the complementary positive roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A standard Levi Weyl subgroup preserves the positive roots outside
its Levi subsystem, in either the full or the indivisible relative roots. -/
def LeviWeylPositiveRootComplementStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    ∀ (R : Set (characterLattice T)), IsRelativeRootAmbient i R →
      ∀ ν : cocharacterLattice T, IsGenericCocharacter i ν →
        ∀ J : Set (characterLattice T), J ⊆ simpleRelativeRoots i ν →
          ∀ w ∈ standardRelativeWeylGroup i ν J,
            let roots := positiveRootSubset R ν \ standardLeviRootSubset R J
            Set.MapsTo (relativeWeylCharacterAction i w) roots roots

end Langlands.GroupScheme
