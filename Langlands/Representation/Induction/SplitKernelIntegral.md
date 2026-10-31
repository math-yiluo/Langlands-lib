# Relative compact-induction coinvariant integration for a split kernel

This pair constructs `Langlands.Induction.splitKernelCompactCoinvariantEquiv`.
It is an internal composition of the actual compact kernel restriction
with the published compact-induction quotient integral and its bijectivity
proof. It was written for the focused prerequisite task
`78e9a565-e0db-4030-a9f9-013bbe8b89b9` of the parabolic-orbit comparison.

Authors: Worker 76 wrote the Lean file and the first version of this text.
Worker 787 checked both against the published Library and edited this text.

## Groups, coefficients, and analytic inputs

Let `G` be a locally compact topological group, `L` a group with a topology,
and `r : G →* L`, `s : L →* G` continuous homomorphisms satisfying
`r (s l) = l`. Let `H` be a closed subgroup of `G` containing every `s l`.
Write

```text
N = r.ker,   I = H.comap N.subtype,
j = N.subtype.subgroupComap H : I →* H.
```

All subgroups carry their actual subgroup topologies. The inducing
representation `σ : Representation ℂ H V` is smooth, with `V` an arbitrary
complex module. No topology, dimension, admissibility, or finite-length
condition is placed on `V`. The universes of `G`, `L`, and `V` are independent.
The topology on `L` need not make it a topological group; the construction
only uses the supplied continuous maps and the topological group operations
of `G`.

`isClosed_splitKernelIntersection` proves that `I` is closed in `N` by
continuous preimage along the kernel inclusion. The homomorphism `j` is
continuous for the two subgroup topologies, as proved by
`continuous_splitKernelInducing`. The published `isSmooth_comp` then proves
`isSmooth_splitKernelInducing`: `σ.comp j` is smooth, without a separate
smoothness premise on this restriction.

For the raw integral and descent, supply a Borel measurable structure on the
actual left quotient `I \ N`, and a measure `ν` finite on compact sets.
Descent uses the explicit hypothesis that every quotient right translation
preserves `ν`. For bijectivity and the final equivalence, additionally supply:

- Hausdorffness of `G` and local compactness of `N`;
- a basis at the identity of `N` consisting of compact open subgroups;
- Borel measurable structures on `N` and `I`;
- regular left and right invariant Haar measures `μN` on `N` and `μI` on `I`;
- `QuotientIntegration.IsCompatible I μN μI ν`.

This last input is the published actual quotient-measure compatibility
condition, including its integration identity and right invariance. The
bijectivity construction uses its `right_invariant` field as the descent
hypothesis. These are intermediate analytic data for an application to
discharge; the pair adds no premise to any parabolic-orbit statement.

## Actual restriction, integral, and quotient formula

Let `E = splitKernelCompactEquiv r s hrs hr hs H hH hsH σ hσ`, the
compact-induction equivalence constructed in `SplitKernelCompact`. It is an
actual equivalence of `N`-representations

```text
((compactInduced H σ).comp N.subtype) ≃ compactInduced I (σ.comp j),
(E f)(n) = f(n).
```

The carriers here are the published `CompactFunctions` subtypes with their
uniform open stabilizer and compact projected support. The construction does
not replace them by locally constant functions with an assumed stabilizer.

`splitKernelCompactCoinvariantRestrictEquiv` applies
`Representation.Coinvariants.map` to `E` and to its inverse. Surjectivity of
the quotient projection reduces the two inverse laws to the inverse laws
of `E`. Thus it gives an actual linear equivalence between the two
coinvariant quotient spaces, without assuming exactness or an unspecified
comparison map.

`splitKernelCompactIntegral` is the composite of restriction by `E` and
`compactCoinvariantIntegral I (σ.comp j) ν`. On a compact function `f`, its
simple-function integrand satisfies

```text
quotientCoinvariantSimple I (σ.comp j) (E f) ([n]) = [f(n)].
```

This is `splitKernelCompactIntegrand_mk`. Projection to the inducing
coinvariants removes the `I`-covariance; it does not assume that `σ` is
trivial on `I`. The raw relative integral has values in
`Representation.Coinvariants (σ.comp j)`. Its formula, recorded by
`splitKernelCompactIntegral_apply`, is the published finite-fiber algebraic
integral of that actual simple function with respect to the supplied `ν`.
It uses no Bochner integral or topology on the values.

The kernel intertwining law for `E` sends right translation of `f` by
`n ∈ N` to ordinary right translation of `E f` by `n`. The published
`compactCoinvariantIntegral_translate` therefore proves
`splitKernelCompactIntegral_translate` from measure preservation of the
quotient right translations.

`splitKernelCompactCoinvariantDesc` composes the induced restriction
equivalence with `compactCoinvariantDesc I (σ.comp j) ν hν`. It is a linear
map from

```text
Representation.Coinvariants ((compactInduced H σ).comp N.subtype)
```

to `Representation.Coinvariants (σ.comp j)`. The lemmas
`splitKernelCompactCoinvariantDesc_mk` and
`splitKernelCompactCoinvariantDesc_mk_integral` identify this same descended
map on every quotient class of `f` with the raw integral and its
finite-fiber formula. Thus the representative formula uses the actual
kernel restriction and actual coinvariant projections.

## Bijectivity and coefficient naturality

The published `compactCoinvariantIntegralBijective` applies to the
topological group `N`, the closed subgroup `I`, the supplied compatible
measures, and the smooth representation `σ.comp j`. Composition with the
bijective induced restriction equivalence proves
`splitKernelCompactCoinvariantDesc_bijective`. The definition
`splitKernelCompactCoinvariantEquiv` bundles precisely this descended map
using `LinearEquiv.ofBijective`. Its target and source are the actual
coinvariant quotients displayed above. Its representative integral formula
is `splitKernelCompactCoinvariantEquiv_mk`.

For every smooth representation `τ` on an arbitrary module `W` in an
independent universe and every coefficient intertwiner `T : σ → τ`, let
`T_I = splitKernelInducingMap r H T`. Naturality before descent follows by
composing `splitKernelCompactEquiv_natural` with
`compactCoinvariantIntegral_natural`. Quotient surjectivity proves the
corresponding descended law. The final theorem
`splitKernelCompactCoinvariantEquiv_natural` states, for every source
coinvariant `z`,

```text
Eint_τ (Coinvariants.map (Jacquet.restrictMap (compactInducedMap H T) N) z)
  = Coinvariants.map T_I (Eint_σ z).
```

Here `Eint` denotes the newly bundled integral equivalence; all maps in the
Lean equation have their explicit source and target representations. This
is compatibility with every coefficient morphism in independent `V` and
`W` universes, not just a choice of objectwise vector-space isomorphisms.
The pair does not yet package a natural isomorphism between normalized
parabolic functors.

## Declarations in order

| Declaration | Content |
| --- | --- |
| `isClosed_splitKernelIntersection` | `I` is closed in `N` |
| `continuous_splitKernelInducing` | `j : I →* H` is continuous |
| `isSmooth_splitKernelInducing` | `σ.comp j` is smooth |
| `splitKernelCompactCoinvariantRestrictEquiv` | coinvariants of `E` and of `E.symm`, as a linear equivalence |
| `splitKernelCompactIntegral` | raw relative integral `f ↦ ∫_{I\N} [f(n)] dν` |
| `splitKernelCompactIntegrand_mk`, `splitKernelCompactIntegral_apply` | its integrand and finite-fiber formula |
| `splitKernelCompactIntegral_translate` | invariance under right translation by every `n ∈ N` |
| `splitKernelCompactCoinvariantDesc` (+ `_mk`, `_mk_integral`) | the descended map and its representative formula |
| `splitKernelCompactIntegral_natural`, `splitKernelCompactCoinvariantDesc_natural` | coefficient naturality before and after descent |
| `splitKernelCompactCoinvariantDesc_bijective` | bijectivity under the compatible-measure inputs |
| `splitKernelCompactCoinvariantEquiv` (+ `_mk`, `_natural`) | the bundled equivalence, its formula and naturality |

The main definition has universe parameters `uG`, `uL`, `uV` (and `uW` in
the naturality theorems). Its development check reports only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Provenance and scope

This is an internal derived construction from `SplitKernelCompact`,
`CompactCoinvariantIntegral`, `CompactCoinvariantBijectivityProof`, the
published smooth pullback theorem, and the actual Mathlib coinvariants API.
No external result is asserted verbatim. Its proof route is composition of
these existing constructions, with the two subgroup-topology helpers and
the explicit representative and naturality laws proved here.

Normalizer or Levi equivariance, Haar character scaling, induction in
stages, normalization-character cancellation, and
`PadicParabolicOrbitJacquetComparison` remain separate obligations. In
particular, this pair alone does not prove the parent Jacquet comparison.
All the dependencies listed above are imported from the published Library
by Lean name; this pair edits none of them.
