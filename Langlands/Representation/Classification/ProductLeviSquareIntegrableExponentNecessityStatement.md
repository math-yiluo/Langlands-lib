# Necessary strict upper Jacquet bounds for square-integrable product Levis

Author: Worker 19.

`Langlands.GLProductLeviSquareIntegrableExponentNecessityStatement.{uF,uV}`
is a closed proposition definition. It supplies no proof. It is the strict
square-integrable counterpart of the published product-Levi tempered
necessity statement, with the irreducibility assumption omitted.

## Analytic input

For every prime `p`, finite p-adic field `F : PadicField.{uF} p`, compatible
topological data `T`, positive rank `n`, and ordered block shape `B`, put
`M = B.Levi F.Carrier` and `Q = M ⧸ Subgroup.center M`. Use the actual product
topology supplied by `T.leviTopologicalGroup B`. Quantify an arbitrary Borel
measurable structure on `Q` and one Haar measure `μ` for that structure.

The input is an actual complex representation `σ` of `M` on a carrier
`V : Type uV` satisfying `IsSquareIntegrableModCenter σ μ`. The universes
`uF` and `uV` are independent. This analytic predicate includes admissibility,
a unitary central character with open kernel acting through the full centre,
and membership of every descended absolute smooth-dual matrix coefficient in
`L²(Q, μ)`. There is no irreducibility, finite-length, finite-dimensionality,
tensor-presentation, or global finite-exponent assumption. The zero carrier
is permitted; it has no generalized eigencharacter witnessed by a nonzero
vector.

## Exponents and chamber

For every actual refinement `D : Geometric.BlockRefinement B`, use
`T.normalizedRefinedJacquet B D σ`. Pull this action back through
`Geometric.flattenedLeviEquiv F.Carrier B D`, then restrict it through the
flattened shape's `blockScalarLevi`. Quantify every character `ψ` of the
flattened scalar group whose kernel is open and which is an
`IsGeneralizedEigencharacter` of this pullback. This definition retains a
nonzero vector killed by one uniform power of all character-defect operators.

Write `e(j,i) = B.flattenBlockEquiv D ⟨j,i⟩`. For a scalar tuple `a`, the
chamber condition is

```text
|a_(e(j,0))| ≤ |a_(e(j,1))| ≤ ...
```

inside every outer block `j`, with `|·| = T.normalizedAbs`. There is no
comparison between distinct outer blocks. The conclusion is `‖ψ(a)‖ ≤ 1`
everywhere in this chamber, together with `‖ψ(a)‖ < 1` if the absolute values
are nonconstant in at least one outer block. All refinements are included.
If every refinement block has length one, the strictness premise is empty;
the weak conclusion still applies.

The normalized action uses the inverse positive half-modulus. Its modulus
on flattened scalars is

```text
δ_D(a) = product_j product_(i<k)
  |a_(e(j,i)) / a_(e(j,k))|^((D j).size i * (D j).size k).
```

In scalar real-part coordinates, the asserted condition is zero total and
strictly positive proper prefixes in each outer block. The weak conclusion
also covers the compact and central directions excluded from the strict
condition.

## Original sources and derived scope

W. Casselman, *Introduction to the theory of admissible representations of
p-adic reductive groups*, draft of 1 May 1995, Theorem 4.4.6, printed/PDF p.45;
coefficient asymptotics and the square-integrability argument on pp.44–45.
Literature ID: `casselman-1995-admissible-representations`; SHA256:
`78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
d'après Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333,
Proposition III.1.1, printed p.263 (PDF29), with normalized exponents in
I.3, printed p.243. Literature ID: `waldspurger-2003-plancherel`; SHA256:
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

The specialization to `M = product_j GL_(B.size j)(F)` is derived from these
general reductive-group formulations. Its standard upper parabolics are the
refinements `D`; its split centre is the product of the scalar centres; and
its simple roots compare refined scalars only within an outer block. An
element lies in the compact split-torus directions times the full centre
exactly when its absolute values are constant separately in every outer
block. Thus the source's removed directions give precisely the strictness
premise above. Unitarity supplies norm one on those removed directions,
which accounts for the weak conclusion there.

Casselman's criterion assumes admissibility with a scalar central character,
not irreducibility. For positive GL blocks the full centre consists of block
scalars, so the analytic central-character datum here is the required one.
The quantification over an arbitrary supplied Borel Haar measure is a derived
choice: the necessity argument uses that measure's invariance and positive
measure of nonempty open subsets, rather than a prescribed normalization.
Neither measure independence nor a Haar adapter is assumed.

The originals and the bounded project errata searches were read during the
parent strict-criterion investigation; no applicable correction was found.
The actual flattened coordinates and the uniform-power definition are the
published Library conventions, not new constructions in this statement.

## Proof obligation and independence

The published `ProductLeviSquareIntegrable.norm_lt_one_of_diagonal` supplies
strictness at suitable noncentral uniformizer test elements. Its
`strictFundHypothesis_of_squareIntegrable` only addresses fundamental
refinements. Neither result alone is this whole-chamber statement.
A proof must also handle arbitrary refinements, the central tests and the
passage from strict proper-prefix inequalities to all nonconstant monotone
tuples. The published real-part and root-cone pairing lemmas suggest that
last step. No implication from `L²` to temperedness is assumed here.

This is an upstream analytic interface for the strict GL exponent criterion.
Its proof must avoid segment analytic classification, multisegment special-head
exhaustion, ordered special-head existence or quotient coverage, tempered block
uniqueness, square-integrable Langlands classification or exhaustion, regular
exhaustion, their conclusions, successors and transitive proof dependencies.
The statement pair imports definitions only; it asserts none of those results.
