# All-regular relative comparison with discrete-series support

This file states the supported GL_n form of the multiplicity equality proved
within Silberger 1978, Lemma 5.6, and its irreducible-head consequence. It is a
proposition definition, not a proof. The intermediate support and positive-root
hypotheses fixed on p.99 are explicit.

## The three actual Levis

Fix a positive rank `n`, a p-adic field `F`, and its compatible local-field
realization `T`. The coarse ordered block shape is `B`. Its refinement `Q`
gives the middle shape `D = B.flatten Q`. A refinement `R` of `D` gives the
fine shape `C = D.flatten R`. A refinement `S` of `B`, with the block-shape
equality `h : C = B.flatten S`, records the same fine blocks directly inside
the coarse Levi.

These data describe a standard nested chain `M ⊆ M' ⊆ M'' ⊆ GL_n(F)`.
Equality of consecutive Levis is permitted. The equality `h` is equality of
the actual ordered block shapes, including their coordinate maps; it is not
an assumed intertwining equivalence or functor compatibility. Lean transports
the fine representation and parameter along this equality. All other
transports use the constructed `flattenedLeviEquiv`. No arbitrary group
equivalence is supplied.

The fine representation `ω` is irreducible, cuspidal, and unitarizable on
`C.Levi F`. Cuspidality includes admissibility and vanishing of the actual
unipotent coinvariants for proper standard refinements. Unitarizability is
existence of an invariant positive definite Hermitian form.

## The positive-root parameter and support hypotheses

`IsPositiveRootParameter D R v₀` expresses the p.99 condition literally as a
strictly positive linear combination of the adjacent simple roots inside
each middle block. If that middle block has fine sizes `d₀,...,d_(r-1)`, the
simple root indexed by `j < r-1` is the fine determinant-exponent vector

`e_j / d_j - e_(j+1) / d_(j+1)`.

The definition supplies a strictly positive real coefficient for every such
root and equates their sum to `v₀`. The factors `1/d_j` convert scalar-block
coordinates to determinant exponents: `|det(z I_d)|^a = |z|^(d a)`.
Thus this is the scalar root `z_j/z_(j+1)`, not an unweighted difference of
determinant exponents. On an unrefined middle block the root set is empty and
the parameter is zero. This explicit expansion also forces the size-weighted
sum of `v₀` to vanish in each middle block.

The middle representation `σ` is irreducible and square-integrable modulo
the full center of `D.Levi F`. It is an actual quotient of the normalized
fine-to-middle induction of `ω |det|^(-v₀)`, witnessed by a surjective
intertwiner.

The coarse representation `π` is irreducible and analytically tempered modulo
the full center of `B.Levi F`. It is an actual quotient of the untwisted
normalized induction of `σ` from the middle Levi. It is also explicitly an
actual quotient of the fine-to-coarse induction of `ω |det|^(-v₀)`, as in
the wording of Lemma 5.6. The latter map follows from the first two support
maps using exactness and induction in stages; retaining it makes the stated
fine quotient hypothesis explicit and does not assume the multiplicity
comparison or the outer quotient.

`IsLeviSquareIntegrable` and `IsLeviTempered` quantify over every Borel Haar
measure on the respective actual central quotient. They wrap the existing
analytic predicates, including admissibility, unitary central character and
the relevant matrix-coefficient integrability conditions. Haar measure exists
by `exists_isHaarMeasure_leviCentralQuotient`, so these hypotheses are not
vacuous. No tensor decomposition or fixed carrier norm is imposed.

## Conclusion and conventions

For every strictly decreasing real coarse exponent vector `t`, put
`πt = π |det|^t` and

`τ = ω ∏ k |det(m_k)|^(-v₀(k) + t(parent(k)))`.

Strict decrease is the regular positive chamber for the upper block
parabolic. The entries of `t` need not each be positive; central shifts are
allowed. There is no relative-genericity hypothesis and no replacement of
strict decrease by weak decrease.

`GLRelativeRegularComparisonStatement` supplies a positive natural number `m`
which is the Jordan–Hölder multiplicity of `τ` both in
`r_(op M)^(M'')(πt)` and in `r_(op M)^G(I_(M'')^G(πt))`. Each multiplicity
predicate supplies a finite composition series with exactly `m` factors
equivalent to `τ`; the conclusion does not identify two potentially empty
series predicates. Both sides retain the outer twist.

It also concludes `HasIrreducibleHead (I_(M'')^G(πt))`: existence of an
irreducible quotient and equality of the kernels of all irreducible quotient
maps. This includes uniqueness when two quotient targets are isomorphic.
An outer quotient or a canonical representative is never a premise.

The inductions are the actual upper normalized inductions with right
translation and positive-half-modulus covariance. Opposite Jacquet modules
are the actual coinvariant modules, normalized by the inverse half of the
opposite full modulus, equivalently the positive half of the corresponding
upper modulus. Silberger's source twist `+i v₀` becomes `-v₀` in determinant
exponents; his outer twist `-i v''` becomes `+t`. The absolute value is the
residue-normalized `q^(-valuation)`.

The independent universes `uF`, `uV`, `uM`, and `uW` belong respectively to the
field, fine representation, middle representation, and coarse representation.
Induced carriers use the maximum of the field and source universes.
Surjective intertwiner witnesses allow differing source and target universes.
The head predicate tests quotient targets in the universe of its induced
source, in accordance with the existing canonical-head definition.

## Source correspondence and proof boundary

A. J. Silberger, *The Langlands Quotient Theorem for p-adic Groups*,
Mathematische Annalen **236** (1978), 95–104: the complete nested support and
positive-root setup on p.99; Lemma 5.5, pp.100–101; Lemma 5.6 and its proof,
p.101. The retained original is
`literature/Silberger (1978), The Langlands quotient theorem for p-adic groups.pdf`,
registered as
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
SHA256 `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
Worker 19 read the complete article and reread pp.99–101, checking the p.99
formula image. No retained erratum was located.

This is an explicitly derived GL_n specialization that retains the supporting
data fixed before the lemma, rather than a general reductive assertion.
The statement includes the equality established inside the proof, not only
the lemma's displayed unique-quotient conclusion. Strict positivity of the
common multiplicity follows from the fine quotient hypothesis and opposite
reciprocity. The strong head conclusion follows by the Lemma 5.5 argument:
two different irreducible quotient kernels give a surjection to the sum of
two irreducible quotients, contradicting the multiplicity equality. Finite
length and nonvanishing provide quotient existence.

The generic constituent comparison does not itself establish this theorem.
The p.101 argument uses continuation of the occurring fine cuspidal classes
and the tempered-exponent cone restriction for induction from the middle
discrete-series representation. Together with the positive-root expansion,
these exclude extra stabilizers at a nongeneric regular positive parameter.
This continuation and cone argument remains a proof obligation. The
[scope audit](../../../notes/jacquet/silberger-lemma53-scope.md) explains why
the unrestricted wording of Lemma 5.3 and Corollary 5.4 cannot be used as
substitutes.

Other proof dependencies include actual normalized induction in stages,
opposite Jacquet transitivity and exactness, finite length, the supported
generic multiplicity equality, and reciprocity and cuspidal extraction in
the correct fixed-central-exponent setting. The statement does not assume
any of these conclusions as fields. It does not prove relative recovery in
Propositions 5.7–5.8, cosocle multiplicities in Proposition 5.9, or the final
Langlands classification.
