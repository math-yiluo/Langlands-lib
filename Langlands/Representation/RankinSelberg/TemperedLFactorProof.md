# L-factors of square-integrable block inductions

Author: Worker 40.

`Langlands.RankinSelberg.temperedLFactor` proves exactly the published
`Langlands.RankinSelberg.TemperedLFactorStatement.{uF,uV,uW}`. For two finite
families of irreducible analytically square-integrable blocks, it constructs
a full symmetric L-polynomial `P` for the actual canonical normalized
inductions and full symmetric L-polynomials `Q i j` for every block pair.
It proves

```text
P = ∏ i, ∏ j, Q i j
```

and `P.eval z ≠ 0` for every complex `z` with `‖z‖ < 1`. No genericity,
polynomial-existence or pole-freeness hypothesis is added.

## Exact scope

The theorem keeps independent field and carrier universes `uF`, `uV` and
`uW`, every prime, canonical p-adic field, allowed nontrivial unitary
additive character and supplied self-dual additive Haar measure. The
dependent block carriers stay in their original universes. Both rank
orders and rank-one blocks are included; each block has rank `m i + 1`
or `n j + 1`. The original finite-family indices and degree-sum equalities
are used unchanged.

The induced representations are exactly
`F.canonicalNormalizedProductInduced (succBlockShape m hm) π` and its
second-family counterpart. The analytic square-integrability predicate
remains the actual matrix-coefficient condition modulo the full center.
The symmetric L-polynomial certificates retain compatible
quotient-measure existence and the normalized-generator condition for
every compatible quotient measure. The statement concerns these actual
inductions and assumes no analytic temperedness predicate.

## Implemented proof

Introduce the quantifiers and four block hypotheses of the unchanged
target, and install the canonical topology. For each block of the first
family apply
`squareIntegrableWhittakerType_of_genericity.{uF,uV}`, supplying the closed
theorem
`Classification.squareIntegrableGenericity.{uF,uV} F F.canonicalTopologicalData`.
Apply the same construction to the second family with the independent
universe `uW`. Each application uses the original block action and its
original irreducibility and analytic square-integrability proofs.

The published adapter derives admissibility and unitarizability, lifts
the actual representation carrier to the universe used by intrinsic
genericity, and transports the result back along the actual representation
equivalence. Published multiplicity one then gives full Whittaker type.
The intrinsic genericity proof uses analytic segment classification and
the actual singleton normalized-induction isomorphism, so no nonzero
Whittaker functional is assumed.

Apply `TemperedLFactorProduct.nonempty_productLPolynomialData` to both
families, their newly obtained full Whittaker type, their original
irreducibility and square-integrability hypotheses, and the closed theorem
`squareIntegrablePoleFree`. The latter proves exactly
`SquareIntegrablePoleFreeStatement.{uF,uV,uW}` and constructs a certified
polynomial with open-disk nonvanishing for any square-integrable block
pair.

The product constructor supplies `ProductLPolynomialData` for these
unchanged inductions and blocks. Return its `inducedPolynomial` and
`blockPolynomial`, then its `induced_spec`, `block_spec`, `product_eq` and
`poleFree` fields. This directly gives every conjunct of the exact target
with the same polynomial witnesses.

## Product construction and provenance

This final module composes published proofs. The mathematical product
argument is implemented in the imported `TemperedLFactorProduct` module
and its algebra, divisibility, gamma and dual dependencies.

The construction first obtains actual normalized L-polynomials and
normalized polynomial residuals from L-divisibility for the original
inductions and the reversed inverse-transpose inductions. Gamma
multiplicativity identifies their original and reflected ratios up to
a nonzero Laurent monomial. Inverse transpose preserves irreducibility
and the actual analytic square-integrability predicate. Closed
square-integrable pole-freeness, transferred by certificate uniqueness,
therefore gives open-disk nonvanishing for both block products. The dual
character uses the self-dual Haar measure at `ψ.scale (-1)` with the
same underlying supplied measure.

Polynomial normalization and cancellation turn the ratio identity into
a reflected residual identity. The reciprocal residue scale has norm
less than one. Reflection rigidity forces both normalized residuals to
equal one, which proves the product equality and transfers block-product
nonvanishing to `P`. The final wrapper discharges every substantive
premise of that construction using the named closed proofs.

The original result is Jacquet, Piatetski-Shapiro and Shalika,
*Rankin–Selberg convolutions*, American Journal of Mathematics 105 (1983),
Proposition 8.4, printed pp.451–452 (one-based PDF pp.86–87), registered
source `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Those pages and the opposite-rank convention in Section 2.12, printed
p.403, were read directly and visually during this task. The proof follows
the source's divisibility, gamma multiplicativity, duality and disjoint
zero-region argument. The source's square-integrable pole input is
Section 8.2(6), printed p.445. The separately published closed proof
supplies that input, and its paired Markdown describes its analytic
proof. With `L(s) = 1 / P(q^(-s))`, open-disk nonvanishing gives the stated
absence of poles on `Re(s) > 0`.
