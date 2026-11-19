# Polynomial product decomposition of finite étale affine-space algebras

`Langlands.Algebra.affineSpaceFiniteEtalePolynomialProduct` proves
`AffineSpaceFiniteEtalePolynomialProductStatement.{u}` in every universe.
It extends the given finite étale algebra to the polynomial ring over the
algebraic closure of the coefficient field. The extension is again module-finite
and étale, so `exists_algEquiv_pi_of_isAlgClosed` identifies it with a finite
power of the new polynomial base as an algebra over that base.

Geometric splitting passes through a finite étale model over a countable
algebraically closed coefficient field. An embedding in ℂ lets the proof use
covering-space lifts from the contractible space ℂⁿ. Integrality bounds each
analytic section on complex lines, where polynomial growth forces it to be
polynomial. The resulting algebraic sections split the complex algebra.
Specialization descends the splitting to the model, and scalar extension
returns it to the algebraic closure in the target proof.

In characteristic zero the algebraic closure is a Galois extension.
In `mvPolynomial_product_of_galois_split`, coefficient extraction commutes
with the semilinear Galois action on the split algebra. Descending the fixed
coefficients expresses the original algebra as a polynomial ring over a
reduced coefficient algebra, which is module-finite by evaluation at the
origin. Decomposing that algebra into fields and commuting polynomials
with its finite product gives the required ring equivalence. The proof
allows zero variables and an empty product.

This implements the geometric splitting and descent described in the
statement's provenance. The splitting argument uses complex analysis and
coefficient specialization, and the descent is carried out directly on
polynomial algebras.
