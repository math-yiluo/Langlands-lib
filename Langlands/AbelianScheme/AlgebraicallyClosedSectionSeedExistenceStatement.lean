import Langlands.AlgebraicGeometry.Picard.FiniteSectionSeed
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Finite section seeds at the unit over an algebraically closed field

This module states the existence of a finite family of line-bundle sections separating
the unit from other rational points and from nonzero rational tangent vectors at the
unit of a commutative smooth proper geometrically connected group scheme. It is a
derived section formulation of the first step of Milne's proof of Theorem 7.1
(Abelian Varieties, p.11). The family may be empty. This module supplies a statement
target, not a proof.
-/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Every commutative smooth proper geometrically connected group scheme over an
algebraically closed field has a finite family of global sections of line bundles
forming a point-and-tangent section seed at its unit. The size `n` may be zero.
This proposition is a statement target, not a proof. -/
def AlgebraicallyClosedSectionSeedExistenceStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (G : Grp (Over (Spec (CommRingCat.of K)))) [IsCommMonObj G.X],
    Smooth G.X.hom → IsProper G.X.hom → GeometricallyConnected G.X.hom →
      ∃ (n : ℕ) (L : Fin n → Langlands.AlgebraicGeometry.Picard.LineBundle G.X.left)
        (s : (i : Fin n) → Langlands.SchemeModule.GlobalSections (L i).obj),
        Langlands.AlgebraicGeometry.Picard.IsFinitePointTangentSectionSeed G.X.hom
          (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X).left n L s

end Langlands.GroupScheme
