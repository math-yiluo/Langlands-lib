import Langlands.Algebra.IntegralLocalLattice
import Langlands.AbelianScheme.HomFiniteFreeStatement
import Langlands.AbelianScheme.HomLocalLatticeProof
import Langlands.AbelianScheme.HomTorsionRestriction

/-! # Finite freeness of actual integral Hom groups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- The actual integral Hom group of abelian schemes over an algebraically
closed characteristic-zero field is a finite free integer module. -/
theorem homFiniteFree : HomFiniteFreeStatement.{u} := by
  intro k _ _ _ A B
  exact Langlands.Algebra.IntegralLocalLattice.finiteFree
    (A ⟶ B) (Hom0 A B) (homToHom0 (A := A) (B := B))
    (Rosati.homToHom0_injective_of_charZero A B)
    (hom_modN_finite A B 2 (by decide))
    (homLocalLattice k A B)

end Langlands.AbelianScheme
