import Langlands.GroupScheme.HomScheme.AdicFiniteDescent
import Langlands.GroupScheme.HomScheme.AdicFiniteTest

/-! # Proof: finite étale descent of the adic Hom comparison -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The finite étale descent step of SGA 3, Exposé IX, Théorème 7.1: the diagonalizable
case of the adic Hom comparison implies the case of a source that becomes diagonalizable
after a finite étale surjective base change. -/
theorem multiplicativeTypeAdicHomDescent : MultiplicativeTypeAdicHomDescentStatement.{u} := by
  intro hdiag A _ _ I _ H G _ ⟨S', p, hfin, het, hsurj, hH⟩
  exact HomScheme.Adic.restrict_bijective_of_finiteEtale p
    (fun ψ hψ hHψ s => HomScheme.Adic.exists_isAlgebraization_affine hdiag ψ hψ hHψ s)
    (fun ψ hψ hHψ s a b ha hb =>
      HomScheme.Adic.eq_of_isAlgebraization_affine hdiag ψ hψ hHψ s a b ha hb)
    hH

end Langlands.GroupScheme
