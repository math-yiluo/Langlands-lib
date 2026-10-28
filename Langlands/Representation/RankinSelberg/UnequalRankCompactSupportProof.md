# Uniform compact support of unequal-rank Whittaker block coefficients

Author: Worker 358.

The theorem
`Langlands.RankinSelberg.unequalRankCompactSupport.{uF,uV}` proves the
unchanged Library proposition
`Langlands.RankinSelberg.UnequalRankCompactSupportStatement.{uF,uV} F T n j k`.
Its parameters are every prime `p`, `F : PadicField.{uF} p`, supplied
`T : F.TopologicalData`, and all natural numbers `n,j,k`. The representation
carrier universe `uV` is independent of `uF`.

This is an internal assembly of two published theorems:

- `Langlands.Whittaker.smoothSimpleRootSupport`, implemented by Worker 657,
  bounds all adjacent diagonal ratios for an actual smooth Whittaker
  coefficient, uniformly over the integral factor.
- `Langlands.RankinSelberg.unequalRankIwasawaSupport`, implemented by
  Worker 676, converts such a bound into one compact rectangular set for
  the actual unequal-rank block matrix.

Their statements, proofs, and the target statement are imported without
modification. The assembly supplies no extra premise for either result.

## Implemented proof

Install the topology, valuation relation, and local-field instances from
the supplied `T`. Fix a character `ψ`, a complex representation `π` of
`GL_(n+j+k+2)(F)` of Whittaker type, its actual Whittaker functional `ℓ`,
and an actual coefficient `f` in `coefficientModel π ℓ`.
Write `r = n + (j+k+1)`.

The Whittaker-type hypothesis includes admissibility, whose smoothness
component is `hπ.1.1`. Applying `smoothSimpleRootSupport` to this component
and `f` chooses a real number `R > 0`. Whenever

```text
f(diagonalUnits a * κ) ≠ 0
```

and `κ` belongs to the integral subgroup for the supplied valuation,
every adjacent ratio satisfies

```text
T.normalizedAbs (a_i / a_(i+1)) ≤ R.
```

The choice of `R` precedes all tuples `a`, integral factors `κ`, and root
indices. Applying `unequalRankIwasawaSupport F T n j k` to this `R`
chooses a compact set `C` of matrices with `j` rows and `n+1` columns.
The Lean proof makes this choice before introducing `g` and `x`.

Now fix `g`, `x`, and nonvanishing of
`f(unequalRankMatrix j k g x)`. The algebraic Iwasawa theorem
`GeneralLinear.Iwasawa.exists_iwasawa`, using a uniformizing element
provided by `exists_isUniformizingElement`, supplies

```text
unequalRankMatrix j k g x = u * diagonalUnits a * κ,
```

with `u` in the actual upper-unipotent subgroup and `κ` in the actual
integral subgroup. The tuple `a_i` is the uniformizing unit raised to the
integer exponent supplied by that decomposition.

The coefficient-model element is already a character-equivariant
function. Its defining property `f.val.property` gives

```text
f(u * (diagonalUnits a * κ))
  = standardCharacter ψ r (u) * f(diagonalUnits a * κ).
```

If the final coefficient on the right vanished, the block coefficient
would vanish, contradicting the fixed nonvanishing premise. Therefore
`f(diagonalUnits a * κ) ≠ 0`. The root-support theorem supplies all the
ratio bounds for these factors. The geometric theorem, applied to the
same factorization and bounds, concludes `x ∈ C`.

## Scope and uniformity

The compact set depends on the coefficient and preceding fixed data,
including `n,j,k`, but is chosen before every `g` and `x`. The factors
chosen after `g,x` do not change that set. Compactness is in the product
topology induced by the supplied `T.topology`; both imported support
theorems use that same supplied data.

Every natural parameter is allowed. With `j=0`, the rectangular space
is a singleton; the imported geometric proof covers it. With `n=0`,
the rectangle has one column. With `k=0`, the trailing identity block
still has size one. No positivity branch in this assembly excludes any
of these cases, including `n=j=k=0`. A zero coefficient has a vacuous
nonvanishing implication. The target's nonzero-functional premise is
retained, although this proof does not need to use it.

The proof uses smoothness from the full Whittaker-type scope and adds
no irreducibility, unitary central character, measure, or analytic
existence assumption. It proves compact support only; finite Schwartz
expansions and the analytic integral conclusions remain separate.

## Original source and provenance

Original: H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics 105
(1983), 367–464. Registered source: `jpss-1983-rankin-selberg`, retained
at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The relevant original pages were read visually during development of
the support interfaces.

The target isolates the Whittaker compact-support consequence used in
the unequal-rank proof of Theorem 2.7 on printed p.393. Section 2.4(3),
p.387, fixes the actual `j` by `n+1` lower-left block and the trailing
identity of size `k+1`. Lemma 2.6, pp.389–390, separates adjacent-ratio
bounds from the geometric entry bounds. Its printed rectangular
dimension label is reversed relative to its displayed block; the
imported target and geometric theorem use the displayed block and the
explicit convention in Section 2.4(3).

The implemented route replaces the stronger torus-expansion input
discussed in Section 2.5, pp.388–389, with the published elementary
smooth root-support theorem. That theorem uses a finite compact orbit,
one common stabilizing lattice, Whittaker equivariance, and the additive
conductor. The geometric proof uses suffix determinants and compact
field balls. Their paired Markdown files describe these internal
derivations. The present file joins their actual conclusions through
Iwasawa decomposition and coefficient equivariance, without invoking
the source's single-gauge estimate or adding its unitary-central-
character restriction.
