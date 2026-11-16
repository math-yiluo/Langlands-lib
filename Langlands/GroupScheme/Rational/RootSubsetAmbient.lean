import Langlands.GroupScheme.Rational.ClosedRootSubsetStatements

/-! # Inclusion of either permitted ambient root set in the actual relative roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} [IsAffineHom G.X.hom]
  {R : Set (characterLattice T)}

/-- Both permitted ambient root sets consist of actual relative roots. -/
theorem IsRelativeRootAmbient.subset_relativeRoots (hR : IsRelativeRootAmbient i R) :
    R ⊆ relativeRoots i := by
  rcases hR with rfl | rfl
  · exact subset_rfl
  · exact fun _ hγ => hγ.1

end Langlands.GroupScheme
