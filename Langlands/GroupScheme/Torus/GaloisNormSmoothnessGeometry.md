# Shear coordinates and geometric smoothness for the Galois norm

Worker 1642, with Worker 1614 contributing the interface and norm proof
decomposition. This is derived infrastructure for the proof of the published
`Langlands.GroupScheme.GaloisNormSmoothnessStatement`. It does not assert that
the Weil restriction has the required coordinates or that the actual norm
has their product formula; the final norm proof supplies those comparisons.

For a finite index type `I`, a chosen `i₀ : I`, and a commutative group `M`,
`shearEquiv` is the multiplicative equivalence

```text
(I → M) ≃* M × ({i : I // i ≠ i₀} → M).
```

Its first coordinate is the product of every input coordinate; its other
coordinates are the unchanged coordinates away from `i₀`. The inverse puts
the first output coordinate times the inverse of the product of the other
output coordinates at `i₀`. Splitting the finite product at `i₀` proves both
inverse laws. The product formula also proves multiplicativity and
`shearEquiv_naturality` under every group homomorphism. No power map or
division by the cardinality of `I` occurs.

The geometric lemmas use actual scheme morphisms. `smooth_fst` identifies
the first projection of a binary product of group schemes with a pullback
of the second factor's structure morphism, so that a smooth second factor
makes the projection smooth. `smooth_of_iso_fst` transports this fact along
an isomorphism in the category of schemes over the base. Its hypothesis
explicitly equates the underlying projection composite with the given
morphism. `smooth_complement` applies the published finite-product
smoothness lemma to the family indexed by the complement of `i₀`.

`smooth_of_baseChange` constructs the cartesian square of an actual
base-changed group-scheme morphism by cancelling the two structure-map
pullback squares. Smoothness then descends using Mathlib's fpqc locality
of smoothness. The construction follows the published
`Langlands.GroupScheme.isIso_of_baseChange` proof in the
`BaseChangeReflection` module with smoothness as its morphism property.
`smooth_of_field_baseChange` specializes this to a
field extension using the published `fieldExtension_fpqc`.

These are internal algebraic consequences of the existing product,
base-change and descent APIs. The motivating finite-Galois norm application
comes from the algebraic smoothness assertion used in Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Lemma 2.5.12, as recorded in the
paired Markdown of the published norm smoothness statement. This helper
implements the shear, projection and descent portion of that derived
argument, without claiming a new literal translation of the source lemma.
