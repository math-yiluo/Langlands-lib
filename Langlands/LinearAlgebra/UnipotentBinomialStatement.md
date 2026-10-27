# Integer powers of unipotent operators

This pair states the two auxiliary assertions used at the end of the proof of
the proposition in Renard, Appendix C.III ("Représentations de Z^d"), printed
pages 279–280, PDF pages 285–286, in the French version dated 9 July 2026. The
registered source is `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The declarations are propositions. They prove neither the auxiliary assertions
nor the matrix-coefficient proposition of C.III.

## Source passage

On printed page 280 the proof writes each block as
`A_j(e_k) = z_k^(j) (Id + N_k^(j))` with `N_k^(j)` strictly upper triangular,
hence nilpotent, and then expands, for `n = (n_1, …, n_d) ∈ Z^d`,

`(Id + N_i^(j))^(n_i) = Id + C(n_i, 1) N_i^(j) + C(n_i, 2) (N_i^(j))^2 + …`,

"la somme étant finie, puisque les N_i^(j) sont nilpotentes". It concludes from
"Les coefficients binomiaux étant des polynômes en les n_i". The exponents
`n_i` are arbitrary integers, so negative powers occur. For a negative integer
the displayed coefficients are the generalized binomial coefficients
`n(n - 1)⋯(n - k + 1) / k!`; this is the only reading under which the expansion
holds, and it is the one used below.

## The unipotent expansion

`Langlands.IntegerUnipotentBinomialStatement` quantifies over every complex
vector space `V : Type u`, an actual unit `g` of the linear endomorphism ring
`Module.End ℂ V`, and every natural number `r` with `(g - 1)^r = 0`. For every
integer `n`, it asserts that the endomorphism underlying the unit power `g ^ n`
equals the finite sum, over `0 ≤ j < r`, of `Ring.choose (n : ℂ) j` times
`(g - 1)^j`. In the source's notation, `g = Id + N` with `N = g - 1` nilpotent.
Multiplication in `Module.End ℂ V` is composition, `1` is the identity, the
scalars act as complex multiples of linear maps, and negative powers are taken in
the actual group of units `(Module.End ℂ V)ˣ`. The equality is an equality of
endomorphisms.

There is no finite-dimensionality, nonzero-carrier, positive-`r` or
nonnegative-`n` premise. The source applies the expansion to finite-dimensional
blocks. The identity only needs the nilpotence of `g - 1`, so this auxiliary is
stated for arbitrary complex vector spaces. This extra generality is internal;
it does not claim a stronger matrix-coefficient theorem. When `r = 0`, the
hypothesis says that the identity endomorphism is zero and the sum is empty; this
case, which includes the zero space, is retained. The statement does not assume
the expansion as a hypothesis.

## Polynomial coefficients

`Langlands.ComplexBinomialCoefficientPolynomialStatement` asserts, for every
natural `j` and complex `z`, that `Ring.choose z j` is the evaluation at `z` of
the complex polynomial `(j.factorial : ℂ)⁻¹ • descPochhammer ℂ j`. Here
`descPochhammer ℂ j` is the product of `X - k` for `0 ≤ k < j`, and the
index-zero polynomial is `1`. The equality holds for all complex inputs. In
particular, at `z = (n : ℂ)` for an integer `n` of any sign, it exhibits the
coefficient `Ring.choose (n : ℂ) j` of the first statement as an ordinary
polynomial in `n`. This is the source's remark that binomial coefficients are
polynomials in the `n_i`. No degree bound is asserted separately.

For the complex numbers, `Ring.choose` is Mathlib's generalized binomial
coefficient. Its `BinomialRing` structure on `ℂ` comes from the instance for
modules over `ℚ≥0` in `Mathlib/RingTheory/Binomial.lean`.

## Aggregate

`Langlands.RenardCIIIUnipotentBinomialStatement` is the conjunction of the two
statements above, with the carrier universe `u` of the first. It adds no
content. It lets one statement record and one later proof cover both targets.

## Errata

The supplementary 2010 errata `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, PDF page 19,
entry for old printed page 322, line −4, adds missing parentheses to the product
`A_j(n) = ∏_i (z_i^(j) (Id + N_i^(j)))^(n_i)`. The governing 2026 text on PDF
page 286 already has these parentheses. The errata correct only the older
edition and leave the binomial expansion itself unchanged; no assertion is taken
from them.

## Scope and possible proof ingredients

The constructions are existing Mathlib objects; no new definition is needed.
In the pinned Mathlib, `Ring.choose_eq_smul` writes `Ring.choose a j`, over a
field of characteristic zero, as `(j.factorial)⁻¹` times the scalar evaluation
`smeval` of `descPochhammer ℤ j` at `a`, and
`descPochhammer_eval_eq_prod_range` gives the product form of the evaluation of
`descPochhammer R j` over a commutative ring. The power-series
identities `PowerSeries.binomialSeries_add` and `PowerSeries.binomialSeries_nat`
are possible ingredients, but this pair supplies no bridge from formal power
series to substitution of a nilpotent element of a noncommutative endomorphism
ring.

The simultaneous generalized-weight decomposition, the scalar-character
factorization, the commuting multivariable product and the adapter from tuples
to matrix coefficients belong to the parent Renard task and are outside this
pair.
