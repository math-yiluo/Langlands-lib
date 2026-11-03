import Langlands.GroupScheme.Absolute.Borel

/-! # The algebraic-closure test scheme -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
namespace Langlands.GroupScheme

/-- The test scheme `Spec k̄ → Spec k` of points with coordinates in an algebraic closure. -/
abbrev algebraicClosurePoint (k : Type u) [Field k] : Over (Spec (CommRingCat.of k)) :=
  (Over.map (toAlgebraicClosure k)).obj
    (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k)))))

end Langlands.GroupScheme
