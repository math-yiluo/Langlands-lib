# Coefficients of a multiplicative Laurent matrix

Worker 37. This internal construction supports the split-rank upper bound for
`U(1,1)`. For a commutative ring `E` and additive commutative monoid `M`, it
defines algebra maps from `E[M]` to `E[M × M]` by the exponent maps `m ↦ (m,m)`,
`m ↦ (m,0)`, and `m ↦ (0,m)`. The coefficient of the diagonal image at `(a,b)`
is the original coefficient at `a` if `a=b`, and zero otherwise. The coefficient
of a left-image times a right-image is the product of the two original
coefficients. The latter identity is proved by linear induction on both
polynomials and the multiplication rule for monomials.

For a finite square matrix `P` satisfying the multiplicativity identity
`P.map diagonalMap = P.map leftMap * P.map rightMap`, let `C m` be its matrix
of coefficients at `m`. Taking the coefficient at `(a,b)` entry by entry gives
`C a * C b = if a=b then C a else 0`. Thus the coefficient matrices are
orthogonal idempotents. This is an elementary derived calculation; no field,
invertibility, characteristic, or nonzero-ring hypothesis is used. The matrix
identity is a hypothesis here; deriving it from the actual torus homomorphism
remains part of the consuming upper-bound proof.

The lemmas `neg_eq_zero_iff` and `neg_ne_zero_iff` apply to a generic matrix
family `C` indexed by an additive group. If a zero-preserving map `c` and an
index function `s` satisfy `C(-m) i j = c(C(m) (s j) (s i))` for every `m,i,j`,
then `C(-m)=0` if and only if `C(m)=0`; hence nonzero support is stable under
negation. One implication is entrywise zero preservation, and the reverse
applies the same implication at `-m`. No injectivity assumption on `c` or `s`
is required, because the hypothesis holds at every exponent. Derivation of
this symmetry from the unitary equation belongs to the consuming proof.
