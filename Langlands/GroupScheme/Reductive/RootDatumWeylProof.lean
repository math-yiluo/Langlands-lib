import Langlands.GroupScheme.Reductive.RootDatumWeylComparison
import Langlands.GroupScheme.Rational.GenericCocharacter
import Langlands.GroupScheme.Rational.PositiveRootStabilizerAveraging
import Langlands.GroupScheme.Torus.MaximalSplitComparison

/-! # The Weyl group of a split maximal torus and its supplied root datum -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The full integral normalizer image is the abstract Weyl image of every
supplied root datum, and the full character-action kernel is the centralizer. -/
theorem weylGroup : WeylGroupStatement.{u} := by
  intro k _ G hG T hT i hi J P hP
  let := hG.isAffineHom
  let := hG.smooth
  let : IsClosedImmersion i.hom.hom.left := hi.2.1
  obtain ⟨ν, hν⟩ := hT.exists_genericCocharacter i
  exact hP.weylImage_and_ker_of_positive_stabilizer hT (hT.finite_relativeRoots i) hν
    (hasTrivialPositiveRootStabilizer i hG (hi.isMaximalSplitTorus hT) hν)

end Langlands.GroupScheme
