import Langlands.GroupScheme.Rational.RealAnisotropicMaximalTorusConjugacyStatement
import Langlands.GroupScheme.Rational.RealAnisotropicCompactConnectedProof
import Langlands.GroupScheme.Rational.RealCompactMaximalTorusConjugacyProof

/-! # Conjugacy of maximal tori in anisotropic real semisimple groups -/

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

/-- Maximal tori of an anisotropic real semisimple group are conjugate by a real point. -/
theorem realAnisotropicMaximalTorusConjugacy :
    RealAnisotropicMaximalTorusConjugacyStatement := by
  intro G hG hA
  let : IsAffineHom G.X.hom := hG.isConnectedReductive.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : CompactSpace (RingPoint ℝ G.X ℝ) :=
    (realAnisotropicCompactConnected G hG.isConnectedReductive hA).1
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology ℝ G.X
  let : CompactSpace (rationalPoints G) :=
    (rationalPointHomeomorph ℝ G.X).symm.compactSpace
  exact realCompactMaximalTorusConjugacy G hG isCompact_univ

end Langlands.GroupScheme
