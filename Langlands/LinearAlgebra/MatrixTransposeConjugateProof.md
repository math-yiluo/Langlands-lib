# Every square matrix over a field is conjugate to its transpose

`Langlands.matrixTransposeConjugate.{uK}` proves exactly the published
`Langlands.MatrixTransposeConjugateStatement.{uK}`. For every field
`K : Type uK`, every natural number `n`, and every matrix `x` over `K` indexed
by `Fin n`, it supplies `g : Matrix.GeneralLinearGroup (Fin n) K` with
`↑g * x * ↑g⁻¹ = x.transpose`. The coefficient field is arbitrary, and rank
zero is included. No hypotheses are added to the statement.

## Implemented proof

The proof imports `Langlands.LinearAlgebra.CyclicQuotientPairingProof` and
uses `Langlands.cyclicQuotientPairing`. This theorem supplies a symmetric,
two-sided nondegenerate bilinear form on `AdjoinRoot q` for every nonzero
polynomial `q`, balanced under multiplication by every quotient element.
The assembly uses its nondegeneracy and balancedness properties.

The private helper `productPairing` sums component forms after coordinate
projections. `productPairing_apply` computes this as the finite sum of their
values. Both nondegeneracy conditions in `productPairing_nondegenerate` follow
by testing vectors supported in one coordinate using `Pi.single`. The same
argument treats an empty index type.

`pairing_of_cyclic_pairings` applies Mathlib's
`Module.equiv_directSum_of_isTorsion` to a finite torsion `K[X]`-module.
The resulting quotients are by powers of irreducible polynomials, so each
defining polynomial is nonzero. Their quotient types and `K`-module structures
agree with `AdjoinRoot`. The cyclic pairings supply the component forms; the
finite direct sum is converted to a product by
`DFinsupp.linearEquivFunOnFintype`. Restricting the polynomial-linear
equivalence to `K` and pulling back the product form gives a nondegenerate
form on the original module. Polynomial-linearity of the equivalence and
multiplicative balancedness on each quotient show that `X` is self-adjoint.

`endomorphism_pairing_of_cyclic_pairings` equips a finite-dimensional
`K`-vector space with the polynomial action `Module.AEval' f`.
Cayley-Hamilton supplies the nonzero annihilator `f.charpoly`, proving that
this module is torsion. Finite generation over `K[X]` follows from finite
dimensionality over `K`. The preceding helper constructs its form. Pulling
back along `Module.AEval'.of f`, and using `Module.AEval'.X_smul_of`, gives
a nondegenerate form for which `f` is self-adjoint.

`conjugate_of_pairing` converts a nondegenerate form `B` on `K^n` to its
Gram matrix `S = B.toMatrix'`. Mathlib's nondegeneracy/determinant equivalence
shows `det S ≠ 0`, so `Matrix.GeneralLinearGroup.mkOfDetNeZero` constructs
a unit `g` with underlying matrix `S`. Self-adjointness identifies
`B.compLeft x.mulVecLin` and `B.compRight x.mulVecLin`. Applying
`BilinForm.toMatrix'` to this equality gives `xᵀ * S = S * x`.
Multiplication on the right by the unit inverse gives `S * x * S⁻¹ = xᵀ`.

`matrixTransposeConjugate_of_cyclic_pairings` combines these helpers for the
matrix endomorphism `x.mulVecLin`. The final theorem applies that assembly
to `cyclicQuotientPairing`, discharging its only hypothesis and proving the
exact published proposition with its single coefficient universe.

## Provenance and scope

This is an internal proof of the matrix fact named by the published statement.
Its companion Markdown records the Bernstein–Zelevinsky 1976 Section 7.3
quotation and explains that the source gives no proof of the classical fact.
The implemented argument follows the cyclic-pairing route in the task context
and that companion Markdown, using Mathlib's PID module decomposition,
Cayley-Hamilton theorem and bilinear-form matrix identities. No source proof
of these intermediate constructions is claimed.

Worker 33 supplied the task and the cyclic-pairing route; Worker 308 implemented
the finite-product, torsion-module, endomorphism and Gram-matrix assembly.
Worker 697 implemented the separately published cyclic pairing proof from
the construction plan supplied by Worker 308. That proof and its statement
are imported by Lean name. This module leaves the target statement and its
import closure unchanged and proves the unrestricted square-matrix result.
