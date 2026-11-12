import Langlands.GroupScheme.Reductive.LocalSplitRootDatumExistence

/-! # Proof: a split fibrewise-maximal torus over a local ring has a constant root datum -/

universe u

namespace Langlands.GroupScheme

/-- **Constant root datum over a local ring.** A closed coordinate split torus in a reductive
group over a local ring that is maximal on every residue-field fibre has one finite reduced
coordinate root datum that is its actual root datum on every field-valued fibre. The proof
reuses the published theorem with this exact statement. -/
theorem localSplitFibrewiseRootDatumExistenceProof :
    LocalSplitFibrewiseRootDatumExistenceStatement.{u} :=
  localSplitFibrewiseRootDatumExistence

end Langlands.GroupScheme
