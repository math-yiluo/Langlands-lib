# L-polynomial divisibility under normalized block induction

Author: Worker 46.

`Langlands.RankinSelberg.lFactorMultiplicativity` proves exactly
`LFactorMultiplicativityStatement.{uF,uV,uW}` from
[MultiplicativityStatement](MultiplicativityStatement.md). It is a closed
theorem with independent field, test-carrier and block-carrier universes.
For the actual ordered normalized upper induction
`F.canonicalNormalizedProductInduced (succBlockShape m h) σ`, it constructs
an induced-pair polynomial `P`, original block-pair polynomials `Pi i`,
their complete symmetric L-polynomial certificates, a polynomial `Q` and
an exponent `e : ℕ` satisfying

```text
X ^ e * ∏ i, Pi i = Q * P.
```

Every canonical p-adic field, nontrivial unitary additive character, supplied
self-dual Haar measure and positive rank in either order remains quantified
as in the statement. The hypotheses are full Whittaker type and permit
reducible representations. The certificates include existence of compatible
quotient measures and validity for every compatible measure.

The Lean proof applies the published
`lFactorMultiplicativity_of_twoBlock` from
[FiniteLFactorMultiplicativity](FiniteLFactorMultiplicativity.md) to the
published closed `twoBlockLFactorMultiplicativity` from
[TwoBlockLFactorMultiplicativityProof](TwoBlockLFactorMultiplicativityProof.md).
The two-block theorem is instantiated at universes
`uF, uV, max uF uW`: the actual induced tail carrier lies in
`max uF uW`. This discharges the finite assembler's sole premise without
identifying the original three universes or adding any hypothesis.

The imported finite assembler inducts on the ordered block family. Positivity
excludes the empty family. In the singleton case, closed symmetric
L-polynomial existence supplies the polynomial and its certificate;
equivalence with singleton induction gives the induced certificate, and the
identity uses `Q = 1`, `e = 0`. For at least two blocks, the induction
hypothesis supplies the tail certificates and cleared identity. Preservation
of full Whittaker type under actual normalized induction permits applying the
two-block theorem to the head and induced tail. Representation equivalences
transport the resulting certificates to the original carriers and induction.
Uniqueness identifies the independently certified tail polynomial. The two
identities compose by adding their exponents and multiplying their quotients,
giving the displayed divisibility direction and all existential witnesses.

The imported two-block proof supplies its analytic comparisons and descent
in every rank order. Its lower-to-upper source transport uses the normalized
opposite-product representation equivalence, reverses the ordered sizes,
dependent carriers and representations together, transports the complete
certificates, and reindexes the block product. The finite assembler then
uses the ordered normalized upper head/tail induction equivalence. These
steps retain the actual induction and its normalization.

This module is an internal composition of the two named Library theorems;
their implementations and mathematical provenance are documented in the
linked companions. The original source statement is Jacquet,
Piatetski-Shapiro and Shalika, *Rankin-Selberg Convolutions* (1983),
Theorem (3.1)(ii), printed pages 404–405, registered as
`jpss-1983-rankin-selberg`, source SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Section 3.2 gives the reduction from two blocks to finitely many; the
implemented assembler groups the head and tail using the published ordered
induction equivalence. With `L = 1/P` and block factors `1/Pi i`, the displayed
equation is precisely the source's Laurent-polynomial membership after
clearing a power of `X`. The target pair and its imports are unchanged.
