import Langlands.Algebra.AffineSpaceFiniteEtaleDecompositionStatement
import Langlands.Algebra.AffineSpaceFiniteEtaleGeometricSplittingProof
import Langlands.Algebra.AffineSpaceFiniteEtaleSplitDescentProof
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Polynomial product decomposition of finite étale affine-space algebras -/

open scoped TensorProduct

namespace Langlands.Algebra

universe u

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem affineSpaceFiniteEtalePolynomialProduct :
    AffineSpaceFiniteEtalePolynomialProductStatement.{u} := by
  intro k _ _ n A _ _ het hfin
  let := het
  let := hfin
  let E := AlgebraicClosure k
  let R := MvPolynomial (Fin n) k
  let S := MvPolynomial (Fin n) E
  obtain ⟨m, ⟨e⟩⟩ := exists_algEquiv_pi_of_isAlgClosed (k := E) (n := n) (A := S ⊗[R] A)
  exact mvPolynomial_product_of_galois_split k E n A m e

end Langlands.Algebra
