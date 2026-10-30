# A balanced nondegenerate pairing on a cyclic polynomial quotient

`Langlands.CyclicQuotientPairingStatement.{uK}` is a proposition. This module
defines it and supplies no proof or chosen bilinear form. The published theorem
`Langlands.cyclicQuotientPairing.{uK}` in
`Langlands.LinearAlgebra.CyclicQuotientPairingProof` proves it.

## Statement

For every field `K : Type uK` and every nonzero polynomial `q : Polynomial K`,
there exists a bilinear form

`B : LinearMap.BilinForm K (AdjoinRoot q)`

with the following three properties, in this conjunction order:

1. `B.IsSymm`: for all quotient elements `u` and `v`, `B u v = B v u`.
2. `B.Nondegenerate`: if `B u v = 0` for every `v`, then `u = 0`, and if
   `B u v = 0` for every `u`, then `v = 0`.
3. For every `a u v : AdjoinRoot q`,
   `B (a * u) v = B u (a * v)`.

Here `AdjoinRoot q` is Mathlib's commutative quotient ring `K[X]/(q)`, with its
canonical `K`-module structure. The form takes values in `K` and is `K`-linear
in each argument. Both products in the last identity are ordinary multiplication
in this quotient. The symmetry and nondegeneracy predicates are Mathlib's
existing `LinearMap.BilinForm.IsSymm` and
`LinearMap.BilinForm.Nondegenerate`.

The only restriction on `q` is `q ≠ 0`: monicity, irreducibility, separability
and positive degree are not assumed. There is no restriction on the field's
characteristic. In particular, a nonzero constant `q` is included. Its quotient
is the zero ring and the zero `K`-vector space; the nondegeneracy predicate means
separation of vectors and therefore permits this case. No nontriviality
hypothesis on `AdjoinRoot q` is imposed.

## Provenance and intended use

This is internal auxiliary mathematics specified for the proof of
`Langlands.MatrixTransposeConjugateStatement`, rather than a quotation from
Bernstein–Zelevinsky. Worker 308 supplied the cyclic-quotient interface and the
construction plan in task `bf6f6ec4-5acb-4816-8539-8f925827d3d7`; Worker 642
formalized the statement and its documentation. The concrete quotient and
bilinear-form predicates come from `Mathlib.RingTheory.AdjoinRoot` and
`Mathlib.LinearAlgebra.BilinearForm.Properties`.

The construction plan for the proof was as follows. If `d = q.natDegree > 0`,
let a linear functional on the quotient take the coefficient of `X^(d-1)` in
the unique representative of degree less than `d`, and apply it to the product
`u * v`. Commutativity and associativity give
the proposed symmetry and balancedness. To separate a nonzero representative
of degree `e < d`, pair it with the class of `X^(d-1-e)`: the product has degree
`d-1`, so its coefficient in that degree is the nonzero leading coefficient of
the representative. Nonzero constant polynomials require the zero quotient
case. This paragraph is a plan, not a Lean proof supplied by this module.

The published proof `cyclicQuotientPairing` implements this plan for monic
`q`. Its functional takes the coefficient of `X^(d-1)` of the remainder
representative chosen by `AdjoinRoot.modByMonicHom`. Because `d - 1` is
natural-number subtraction, the same definition covers the zero quotient of a
monic constant. An arbitrary nonzero `q` is then reduced to its monic
normalization. The form is pulled back along the `K`-algebra equivalence
`AdjoinRoot.algEquivOfAssociated` between the two quotients.
Transport to finite direct sums and assembly of a matrix conjugator are done
downstream, in the published proof `Langlands.matrixTransposeConjugate` of
`Langlands.MatrixTransposeConjugateStatement`, which uses
`cyclicQuotientPairing`.
