# The JPSS unequal-rank block-zero rational functional equation

Author: Worker 112.

`Langlands.RankinSelberg.unequalRankBlockZeroGammaExistence` proves exactly
`UnequalRankBlockZeroGammaExistenceStatement.{uF,uV,uW} F T n r`.
Its binders are the prime parameter and its primality instance,
`F : PadicField.{uF} p`, the supplied `T : F.TopologicalData`, and natural
numbers `n,r`. The field and both representation-carrier universes remain
independent.

For every `n < r` and all data quantified by that statement, the conclusion
provides one nonzero rational function `G` before the coefficient vectors.
It includes a model-minus-one scalar, a nonzero actual original rational
value, and rational continuations of both actual integral families satisfying
the gamma equation for every coefficient pair. All analytic and uniqueness
inputs are discharged by imported published theorems.

## Implemented proof

The Lean proof applies the published
`UnequalRankBlockZeroGammaAssemblyInput.gammaExistence`. Its input is a
conjunction of three universal propositions. The three components are:

1. `fun j k => unequalRankAnalytic.{uF,uV,uW} F T n j k`.
   This proves all four analytic clauses for every rectangular block:
   absolute convergence, rational continuation of the actual integrals,
   a common denominator, and normalized-generator existence.
2. `unequalRankBlockZeroContinuedForms.{uF,uV,uW} F T n r`.
   This constructs bilinear forms from the original and dual continuations,
   outside a finite set chosen before the varying spectral parameter, and
   proves their actual general-linear and unipotent covariance laws.
3. `unequalRankBilinearUniqueness.{uF,uV,uW} F T n r`.
   This proves proportionality of the covariant forms in the full
   Whittaker-type scope.

The second theorem's original and dual analytic premises are supplied
inside the assembly from the first component. They are not premises of
the final theorem.

The reused assembly installs the topology and measurable structures from
`T`, derives Whittaker type of both actual inverse-transpose representations,
and derives nonvanishing of their dual functionals. It specializes the
analytic theorem to complementary blocks `(0,k)` and `(k,0)`, where
`k = r-n-1`, with the same supplied quotient measure `mu` and scalar
Haar measure `nu`. It then supplies the continued forms and fixed-data
uniqueness to `exists_blockZeroGammaEquation_of_analytic`.

That published extraction selects continuations of the actual integrals.
Normalized-generator existence gives a nonzero original value and a
separate nonzero dual value. The actual translated first dual-model
equivalence and surjective second dual-model map pull the latter witness
back to original-model vectors. The witnesses need not use the same
coefficient pair. The model-minus-one scalar is derived from the smaller
representation's Whittaker type.

The reused bilinear comparison obtains rational cross identities from
covariance and uniqueness off a finite exceptional set. At a parameter
where the original form is zero, the cross identity follows directly;
otherwise uniqueness makes the dual form a scalar multiple of it.
Rational continuation and spectral comparison turn these identities into
rational-function identities. The two separate nonzero witnesses then
produce one nonzero `G`. This avoids assuming a coefficient pair with
simultaneously nonzero original and dual evaluations.

## Full Whittaker-type scope

The imported `unequalRankBilinearUniqueness` proves the extension required
by this target, including reducible representations. Its companion
`unequalRankSourceLengthBound` combines the published mirabolic finite-length,
irreducible pairing-rigidity and compact/generic pairing theorems through
the finite-length functional-factor assembly. The source form space has
length at most one away from a finite spectral set. Pullback along the
two surjective coefficient-model maps is injective, preserves both
covariance laws, and descends proportionality to the actual coefficient
models. Thus the irreducible generic proposition on JPSS p.399 is not
treated as already having the target's full scope.

The exact target retains arbitrary supplied compatible quotient measure
and self-dual scalar Haar measure, specified nonzero functionals, and all
Whittaker-type data. The two rectangular measures are
`rectangularMeasure nu 0 (n+1)` and `rectangularMeasure nu k (n+1)`.
The dual integral retains the complementary block, the character
`psi.scale (-1)`, the inverse-transpose coefficient models, and
`blockWeylAt n r hnr` right translation of the first transformed function.
The actual integral exponent remains `s-(r-n)/2`.

Writing `x(s) = spectralPoint q s`, the resulting equation is

```text
Rdual(x(1-s)) = zeta^r * (G(x(s)) * R(x(s))).
```

It holds with all three reduced-denominator conditions of
`GammaFunctionalEquation`: for `R` at `x(s)`, `Rdual` at `x(1-s)`, and
`G` at `x(s)`. Here `r` is the larger rank minus one. The target includes
the cases `n=0` and `r=n+1`.

## Original source and derived assembly

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464, registered as `jpss-1983-rankin-selberg`.
The retained scan is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed pp.398–403, one-based PDF pages 33–38, were read completely and
visually for this proof. The current registration has no erratum pointer,
and no applicable erratum was found in the checked project literature and
note locations.

Section 2.11, p.398, formula (1) is the block-zero quotient integral.
Formula (2) gives its general-linear covariance and that of the
complementary transformed integral. Formula (4) on p.399 gives the
additional unipotent covariance. The paragraph following (4) deduces
the block-zero functional equation from uniqueness. The proposition
and mirabolic lemma on p.399 explicitly assume irreducibility; their
proof on pp.400–403 uses distributions, support reduction and induction.
The printed ranks are `r+1,n+1` in Lean.

This final module is derived assembly of published proofs of those exact
analytic, covariance and extended-uniqueness interfaces. Their paired
Markdown files explain the implemented constituent arguments. It does
not reproduce the distribution argument or assume the parent's final
functional equation. The target and all imported Lean/Markdown pairs
are unchanged. Propagation to other blocks and epsilon normalization
are separate results.
