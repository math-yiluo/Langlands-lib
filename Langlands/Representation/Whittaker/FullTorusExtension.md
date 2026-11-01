# Extending the Whittaker expansion to the full diagonal torus

Author: Worker 78.

`Langlands.WhittakerFullTorus.of_lastEntryOne` proves the implication from
`WhittakerLastEntryOneAsymptoticStatement.{uK,uV}` to
`WhittakerTypeAsymptoticStatement.{uK,uV}`. The field and carrier universes
remain independent. The separate closing module `TypeAsymptoticProof`
discharges its sole premise with the published last-entry-one theorem.

This is an internal derived extension of JPS (1979), Proposition (2.2) and
Remark (2.2.5), printed pp.181–183. It uses the one-dimensional space of
Whittaker functionals to obtain a common character on coefficient images.
The target's Markdown describes another extension using a finite scalar
operator algebra; the present proof uses the more direct coefficient law.
It imposes no scalar-action assumption on the original carrier.

## Diagonal normalization and finite functions

For a field `K` and rank `n+1`, `lastCoord` is evaluation at the last
entry, and `normalize` divides each entry by that entry. They are monoid
homomorphisms. `normalize_last` makes the final normalized entry one;
`roots_normalize` preserves the exact consecutive-quotient root coordinates.
The module reuses `WhittakerLastEntryOne.torus` and
`WhittakerLastEntryOne.roots` from `LastEntryOneAssembly` for the exact
diagonal homomorphism and root coordinates.
`torus_factor` and `torus_factor_left` prove

```text
torus(a) = scalar(a_last) * torus(normalize(a)).
```

Both coordinate maps are continuous over a topological field. The scalar
map into the actual center is continuous by `scalarContinuous` and the
subtype topology. `canonical_continuous_normalize` checks the normalization
map using the topology, valuation relation and local-field instances from
the same canonical topological data as the target.

The reused `WhittakerLastEntryOne.IsFiniteFunction` is exactly continuity
together with finite-dimensional complex span of left translates. The
pullback and product wrappers are added in that same namespace and use
the published `RankinSelberg.finiteFunctionClosure`. Consequently, if
`eta` and `chi` are finite functions, so is

```text
a ↦ eta(lastCoord(a)) * chi(normalize(a)).
```

## A common character for all eligible functionals

`scalarCharacter_of_spanning_functional` starts from a smooth representation
and a nonzero functional spanning its full equivariant-functional submodule.
Multiplication by this functional defines a linear map from the complex
field onto that submodule. Nonvanishing proves injectivity. Its inverse
therefore supplies the linear equivalence with the complex field required
by `Whittaker.CoefficientCentralCharacterStatement`.

The supplied character theorem yields one locally constant character of the
actual group center acting on every coefficient image. Composing it with
`GeneralLinear.scalarToCenter` and the inclusion of complex units produces
a continuous monoid character `eta : Kˣ →* ℂ`.
`functional_scalarLaw_of_coefficientLaw` evaluates the coefficient-image law
on `Whittaker.modelMap rho ell v` at the identity, obtaining

```text
ell(rho(scalar(z)) v) = eta(z) * ell(v).
```

The character is shared by every eligible functional. This statement does
not require the scalar matrix to act as a scalar on the original carrier.
The adapter takes the character proposition explicitly; `of_lastEntryOne`
discharges it with the published `Whittaker.coefficientCentralCharacter`.

## Uniform assembly and collisions

`extend_of_coefficient_character` takes the last-entry-one expansion with
finite set `X`, and the common character law above. It chooses the image
of `X` under

```text
chi ↦ (a ↦ eta(a_last) * chi(normalize(a)))
```

before introducing the functional and vector. The character is itself a
finite function by the character clause of `finiteFunctionClosure`, and
pullback and product closure prove the same property for every image
function.

For each functional and vector, take its reduced Schwartz–Bruhat
coefficients. Factor the full torus element with the scalar first, use the
functional scalar law, and apply the reduced formula to `normalize(a)`.
The unchanged roots allow the same coefficients on all additive `Kⁿ`.

`regroup` handles any equal image functions. The coefficient at an image
function is the finite sum of the original coefficients over its fiber.
It remains in the Schwartz–Bruhat submodule. Mathlib's
`Finset.sum_fiberwise_of_maps_to` identifies the two sums. No injectivity
of the transformation of finite functions is assumed.

## Exact closed-proposition reduction

`of_lastEntryOne` installs the target's canonical topology, valuation and
local-field instances and introduces its unchanged telescope. It uses
`Whittaker.mem_functionals_entrywiseCharacter_iff_entrywise` to identify
the target's explicit matrix covariance with membership in the actual
Whittaker-functional submodule. This transfers the nonzero spanning
functional and the scalar law without modifying the target.

Smoothness follows from admissibility. The published coefficient-character
proof supplies `eta`, and the given reduced proposition supplies `X` and
all reduced coefficients with exactly the original hypotheses. Applying
`extend_of_coefficient_character` then gives precisely the full-torus
conclusion. There is no irreducibility, finite-dimensional original
carrier, unitary central-character or positive-root-rank premise.
In particular `n=0`, corresponding to rank one, uses the same normalization
and finite-family assembly on the one-point root-coordinate space.

## Source provenance

The original registered source `jps-1979-gl3-i` is H. Jacquet,
I. I. Piatetski-Shapiro and J. Shalika, *Automorphic forms on GL(3) I*,
Ann. of Math. (2) 109 (1979), 169–212, SHA256
`6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.
Proposition (2.2), its proof, Lemma (2.2.1) and Remark (2.2.5), printed
pp.181–183 (PDF14–16), were read during this task. They supply the reduced
expansion and the admissible finite-type scope. The normalization,
coefficient-character route and collision bookkeeping above are derived
internal arguments, rather than an assertion that the source prints this
full-torus proof.
