# Closed-embedding independence of full adelic growth conditions

`Langlands.Automorphic.GroupSchemeFunctions.closedImmersionAdelicGrowthIndependence`
proves the existing
`ClosedImmersionAdelicGrowthIndependenceStatement` at its arbitrary universe
`u`. For every number field `F`, actual affine group scheme `G` over
`Spec F`, positive ranks `N` and `M`, and two scheme-theoretic closed matrix
embeddings `rho` and `sigma`, it proves both ordinary growth equivalences
on every original `ContinuousRationalFunctions F G` and both uniform growth
equivalences on every original `FinitePlotSmoothRationalFunctions F G`.
The uniform comparisons retain the same relative dimension, smooth structure
`hsmooth`, scalar commutator premise `hcalc`, enveloping algebra, function,
and `adelicEnvelopingAction`.

## Bounds from the published domination theorem

The proof imports `Langlands.Global.AdelicRepresentationHeightDominationProof`
and uses its theorem `RepresentationGrowth.closedImmersionAdelicHeightDomination`
twice. Write `H_rho(g)` and `H_sigma(g)` for the existing
`RepresentationGrowth.adelicHeight` values. The closed immersion `rho`
gives `A >= 1` and a natural `e` such that

```text
H_sigma(g) <= A * H_rho(g)^e
```

for every full adelic point `g`. The closed immersion `sigma` gives `B >= 1`
and a natural `l` such that

```text
H_rho(g) <= B * H_sigma(g)^l.
```

These constants and exponents are chosen before the point and before any
enveloping element. Domination is a proved imported theorem, with no
additional premise in the theorem being proved. Positive rank also gives
`1 <= H_rho(g)` and `1 <= H_sigma(g)`.

The private scalar lemma `transfer_height_bound` implements the inequality

```text
0 <= H,  0 <= C,  H <= A*K^e,  b <= C*H^k
  imply  b <= (C*A^k)*K^(e*k).
```

It raises the domination inequality to the natural power `k`, multiplies
by the nonnegative coefficient `C`, and rewrites powers of products and
iterated powers. Thus a polynomial-growth bound for `rho` with coefficient
`C` and exponent `k` gives one for `sigma` with coefficient `C*B^k` and
exponent `l*k`. The reverse direction uses coefficient `C*A^k` and exponent
`e*k`. These coefficients are nonnegative. Each bound evaluates the same
original function at the same full adelic point.

## Uniform quantifiers and real exponents

For uniform polynomial growth, begin with a single natural exponent `k`
that bounds all enveloping derivatives. In the forward direction the proof
chooses `l*k` before introducing an arbitrary enveloping element `a`.
Only then does it extract the coefficient `C` for `a` and replace it by
`C*B^k`. In the reverse direction it chooses `e*k` first and replaces each
derivative coefficient by `C*A^k`. The scalar lemma applies to the norm of
`evaluate F G (adelicEnvelopingAction F G hsmooth hcalc a f).val g`.
Consequently the exponent remains common to all enveloping elements, and
only the coefficient depends on the element.

The ordinary real-exponent equivalence is the composition of
`hasAdelicModerateGrowth_iff` for `rho`, the proved polynomial equivalence,
and the inverse of `hasAdelicModerateGrowth_iff` for `sigma`. The uniform
real-exponent equivalence uses `hasAdelicUniformModerateGrowth_iff` in the
same way. These existing conversions relate the dimension-scaled full
height to the exact `adelicSourceNorm` by the positive rank-dependent
scalar `N^(sum v, v.mult)`. They preserve the original local
matrix/inverse-entry maxima and infinite-place multiplicities. Thus the
proof establishes the stated real-exponent source-norm predicates as well
as the natural-exponent height predicates.

## Provenance and scope

This is an internal consequence of the published full adelic domination
theorem and the existing real/natural conversion theorems. The
[statement Markdown](GroupSchemeAdelicGrowthIndependenceStatement.md)
records the source motivation: Getz and Hahn, *An Introduction to
Automorphic Representations* (2024), equations (6.3)-(6.4) and (6.7)-(6.8),
Definition 6.3.1, and Exercise 6.1 (printed pp.158-159, 161-162, 179-180;
PDF pp.172-173, 175-176, 193-194). The retained October 2026 author errata
makes no correction to these formulas, definition, or exercise.

As in the target, this result concerns the Library's affine group schemes,
explicit closed embeddings, and original function carriers. The uniform
predicate extends the source bound to the finite plot-smooth carrier;
there is no identification here with the algebraic tensor product in
GH (6.1). The proof introduces no reductivity, connectedness, additional
domination, or global finite-tensor hypothesis. Equality of growth
subspaces and comparison maps remain subsequent consumer constructions.
