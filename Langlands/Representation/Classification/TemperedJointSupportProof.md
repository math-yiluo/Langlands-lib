# Joint fine, middle and coarse support of tempered product-Levi representations

Author: Worker 517. Support-interface and dependency audit: Worker 711.

`Langlands.glTemperedJointSupport` proves exactly the closed proposition
[`Langlands.GLTemperedJointSupportStatement.{uF,uV}`](TemperedJointSupportStatement.md).
The field universe and original carrier universe are independent. Its only
representation hypotheses are irreducibility and the existing analytic
temperedness predicate for the given product Levi.

The proof assembles three published closed results. It introduces no new
support or analytic hypothesis and constructs no replacement representation
for the given coarse representation.

## Middle support and fine support

Apply
[`glTemperedLeviUpperSupport`](TemperedLeviUpperSupportProof.md)
to the given representation `π` on `B.Levi F.Carrier`. It produces
`Q : BlockRefinement B`, an irreducible representation `σ` on the flattened
middle Levi `D := B.flatten Q`, analytic square-integrability modulo its
full center, and a surjective intertwiner

```
qMC : (middleInduced T B Q σ).ρ → π.ρ.
```

The arrows in this explanation denote actual representation intertwining
maps. The imported theorem derives its tensor presentation and analytic
properties from the original hypotheses; it includes the required
opposite-to-upper comparison and constructs the quotient to the original
coarse carrier.

Apply
[`glDiscreteSeriesPositiveRootSupport`](DiscreteSeriesPositiveRootSupportProof.md)
to that same `σ`, using its irreducibility and square-integrability. It
produces a refinement `R` of `D`, an irreducible cuspidal unitarizable
representation `ω` on `(D.flatten R).Levi F.Carrier`, a parameter `v₀`
satisfying the exact `IsPositiveRootParameter D R v₀`, and a surjective
intertwiner

```
qFM : (innerInduced T D R (fineTwist T D R ω v₀ 0)).ρ → σ.ρ.
```

The imported positive-root condition is the strict expansion in adjacent
scalar roots with reciprocal fine sizes, including the empty expansion for
an unrefined block. Unitarizability is the existence of an invariant positive
definite Hermitian form. Both properties are conclusions of the imported
closed support theorem.

## The composite refinement and the direct quotient

Choose the actual refinement and literal ordered-shape equality

```
S := B.composeRefinement Q R
h := B.flatten_composeRefinement Q R
```

so that `h : D.flatten R = B.flatten S`. The quotient-transport clause
of
[`normalizedNestedInduction`](NestedInductionProof.md)
applies to the same `Q`, `R`, `ω`, `v₀`, `σ`, `π`, `qFM`, and `qMC`.
It constructs a surjective intertwiner

```
qFC :
  (innerInduced T B S
    (fineTwist T B S (h ▸ ω) (h ▸ v₀) 0)).ρ → π.ρ.
```

Its implementation induces the surjective `qFM`, composes with `qMC`,
and precomposes with the inverse of the actual normalized induction-in-stages
equivalence. It proves the needed smoothness and preservation of
surjectivity internally. Its transport lemma identifies this source with
the displayed fine twist after transporting both the representation and
parameter along the same `h`.

The final existential tuple retains these three maps and their
surjectivity proofs together with the original support data. The direct
map therefore uses the same fine representation and parameter as `qFM`.

## Universes, conventions and provenance

Upper support is instantiated at `uF,uV`. Its middle carrier lies in
`Type (max uF uV)`, so fine support is instantiated at
`uF,max uF uV`. Its output carrier has universe
`max uF (max uF uV)`, which reduces to `max uF uV`. Nested quotient transport
is instantiated at `uF,max uF uV,max uF uV,uV`. The coarse target retains
its original carrier in `Type uV`; no universe equality is imposed.

The proof uses the analytic predicates unchanged: temperedness and
square-integrability quantify over all Borel Haar measures on the quotients
by the respective full product Levi centers. The fine determinant exponent
remains `-v₀`, since the coarse parameter in `fineTwist` is zero.
All three sources use the existing normalized upper refined induction,
with positive-half-modulus covariance, right translation and
`q^(-valuation)` absolute values.

This is an internal logical assembly of the three named Library proofs.
The source motivation and its normalization are documented in the paired
statement: Silberger 1978, printed pp.96–99, especially the support setup
at the start of the proof of Proposition 5.1 on p.99. The support proofs
explain the derived product-Levi, analytic, unitarization and upper-quotient
comparisons; the nested-induction proof explains the actual subgroup,
modulus and equality transports. This module adds only their joint
existential assembly.

The constituent restriction in
[`silberger-lemma53-scope.md`](../../../notes/jacquet/silberger-lemma53-scope.md)
is preserved. The proof establishes no unrestricted multiplicity comparison,
relative recovery, regular head, uniqueness or classification assertion.
