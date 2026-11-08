# L-factors of genuine Langlands standard modules

Author: Worker 111.

`Langlands.RankinSelberg.langlandsTypeLFactor` proves exactly the closed
`Langlands.RankinSelberg.LanglandsTypeLFactorStatement.{uF,uV,uW}`.
For every prime, canonical p-adic field, unitary additive character, supplied
self-dual Haar measure and two genuine positive-rank tempered Langlands data,
it constructs a polynomial for their actual standard modules and polynomials
for every pair of their actual twisted blocks. It returns the existing full
symmetric and arbitrary-rank L-polynomial certificates and proves that the
standard-module polynomial equals the double product of the block polynomials.
The field and the two block-carrier universes remain independent. The target
statement and its imported Lean/Markdown pairs are unchanged.

The auxiliary public theorem `langlandsTypeLPolynomial_product` gives the
product equality for any supplied certified polynomials of these same actions.
It is a consequence used by the closed existence theorem, rather than a
replacement for its existence conclusion.

## Implemented proof

Write the block exponents as strictly decreasing real families `u_i` and `v_j`,
and write `q > 1` for the residue cardinality. The constructor
[`langlandsTypeLPolynomialData`](LanglandsTypeLPolynomialData.md) supplies a
certified standard-module polynomial `P`, certified twisted-block polynomials
`Q i j` and a normalized residual `D` such that

`B = product_i product_j Q i j = D * P`, with `D.coeff 0 = 1`.

This constructor derives full Whittaker type from the irreducible analytically
tempered blocks, real determinant twists and normalized upper induction. Its
analytic adapter uses closed tempered exhaustion and square-integrable
genericity results. Thus Whittaker type, rationality, block-factor existence
and classification results are not caller hypotheses in the final theorem.
The certificates retain their complete quotient-measure and normalized-generator
conditions and the supplied character and Haar measure.

The private proposition `ProductBelow N` states the product equality for all
certified pairs with total block count below `N`. It quantifies over the
character, its self-dual Haar measure, arbitrary ranks and genuine data, while
keeping the two carrier universes in their original order. Rank zero is
excluded by the polynomial certificate. Strong induction proves this proposition
for every `N`. Quantifying character and measure is necessary because the
reversed data use the inverse character, together with the existing certificate
that the same measure is self-dual for it.

For a pair at the current block count, delete the first block on the second
side when that side has at least two blocks. The genuine tail has positive rank
and strictly smaller length. The same closed constructor supplies its polynomial
`Ptail`, and induction identifies it with the product `A` of all the remaining
columns. The actual head/tail equivalence and the closed
[`langlandsStandardTailLPolynomial_dvd`](LanglandsTypeTailDivisibility.md) give
`A` dividing `P`. The symmetry of the rank relation handles deletion on the
second side without interchanging the induction's carrier universes.
Writing `B = A * C`, where `C` is the first-column product, and cancelling the
nonzero polynomial `A` in `B = D * P` gives `D` dividing `C`.
Nonzeroness follows from the constant term one of every block polynomial.
When the second side has one block, `C = B` and divisibility follows directly
from the residual factorization. The same argument deleting the first block on
the first side proves that its residual divides the first-row product.

For every actual pair of blocks,
[`analyticTemperedTwistLPolynomial_poleFree`](AnalyticTemperedTwistLPolynomialData.md)
gives

`(Q i j).eval w != 0` whenever `norm w < q^(u_i + v_j)`.

A positive-rank adapter applies this theorem to block sizes that are not
syntactically successors. The antitonicity of the exponent families and
monotonicity of `q^x` imply that the first-column product is nonzero in the
disk of radius `a = q^(u_last + v_first)`. Since `D` divides that product,
`D` is nonzero in the same disk.

Now use the closed
[`langlandsTypeReflectionData`](LanglandsTypeReflectionData.md) constructor.
It supplies the original certified data, the certified data for the genuine
reversed inverse-transpose Langlands data, and the identity

`D(X) = c * X^m * E(q^(-1)/X)`

in the rational function field, for a nonzero complex coefficient `c` and an
integer `m`. Here `E` is the normalized residual for the reversed pair. The
constructor transports complete certificates through actual standard-module
and twisted-block equivalences; it makes no identification of a reducible
standard module with its smooth dual.

Apply the first-row divisibility argument to the reversed pair using the same
induction hypothesis: reversing preserves block counts. Its first-row product,
and hence `E`, is nonzero in the disk of radius

`b = q^((-u_last) + (-v_first)) = q^(-(u_last + v_first))`.

Both radii are positive, their product is one, and the norm of the reciprocal
residue scale is strictly less than one. The closed
[`reflectionRigidity`](ReflectionRigidityProof.md) theorem therefore gives
`D = 1` and `E = 1`. Its hypotheses are precisely the two normalized constant
terms, these two disk bounds and the displayed rational identity. Substitution
in `B = D * P` gives `P = B`. Uniqueness of the full polynomial certificates
transfers the equality from the constructed reflection data to any supplied
certified `P` and `Q` and closes strong induction.

Finally `langlandsTypeLFactor` invokes `langlandsTypeLPolynomialData` for the
original data, retains all its witnesses and complete certificates, and applies
`langlandsTypeLPolynomial_product`. It adds no hypothesis to the target.

## Source and provenance

The target is Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg
convolutions* (1983), Proposition 9.4, display (3), printed page 458; the
statement's source identifier is `jpss-1983-rankin-selberg`, with SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The original page states the product over all block pairs, with normalized
upper-parabolic induction and strictly decreasing real exponents. Section 8.4,
printed page 451, supplies the source's square-integrable induction description
of tempered representations; the analytic-tempered bridge used here is proved
by the imported adapters.

The original proof, printed pages 458–462, uses induction, tail divisibility,
reversed Langlands data, a functional equation modulo a unit, and the pole
bounds from Section 8.4. In particular displays (16)–(23), printed page 461,
and the pole contradiction at the top of page 462 correspond to the boundary
column/row cancellation and reflection step here. The implementation packages
that contradiction as nonvanishing on reciprocal disks and polynomial
reflection rigidity. It uses one strong induction on the total block count,
including the one-block cases, rather than separate base and double inductions.
This is an internal proof assembled from the named closed Library results;
no external assertion or additional classification premise is introduced.
