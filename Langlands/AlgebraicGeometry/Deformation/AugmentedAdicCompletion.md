# The actual augmented adic completion and its Artinian maps

This internal algebra construction works at every universe `u`. Let `k` be a
commutative ring, let `K` be a field with its given `k`-algebra structure, and let
`R` be a commutative noetherian local `k`-algebra. Fix a surjective `k`-algebra
homomorphism `ε : R →ₐ[k] K`. No section of `ε` or coefficient-field structure on
`R` or on a test algebra is assumed.

All declarations below lie in
`Langlands.AlgebraicGeometry.Deformation.AugmentedAdicCompletion`.

## Constructed objects

`ring` is Mathlib's actual completion `AdicCompletion (IsLocalRing.maximalIdeal R) R`.
`sourceMap` is the original scalar-preserving canonical map `R →ₐ[k] ring`.
Mathlib supplies the local ring structure and completeness for its maximal ideal.
The present module imports only published local-completion and actual-Artinian-test
interfaces; it does not depend on the separate completion-noetherianness candidate.

`residueFactor` factors `ε` through `R / maximalIdeal R` using the equality of its
kernel with the actual maximal ideal. `augmentation` composes this factor with the
completion's first quotient evaluation. `augmentation_sourceMap` proves the exact
triangle with `ε`, and `augmentation_surjective` proves surjectivity by lifting an
element first to `R` and then mapping canonically into the completion.

For every `n : ℕ`, `projection ε hε n` maps the completion to the actual
`LocalAdicArtinianTests.test ε hε n`, whose ring is `R / m^(n+1)`. The equations
`projection_sourceMap`, `projection_transition` and `augmentation_projection`
identify its canonical source composite, compatibility with every later-to-earlier
transition, and original specified residue augmentation. `projection_surjective`
records actual surjectivity.

`ker_projection` identifies its kernel with the `(n+1)`st power of the completion's
actual maximal ideal. `exists_approximation` consequently proves that every
completion element differs from the image of some original element by an element
of any specified positive maximal-ideal power.

## All compatible maps, with natural comparison

For an actual `ArtinianTest k K` object `A`, `Maps ε A` contains **all** `k`-algebra
homomorphisms `R →ₐ[k] A.algebra` satisfying the augmentation equation.
`postcomp` uses every actual augmented test arrow. `restriction` precomposes with
`sourceMap` and preserves that equation.

`extensionAt α n hn` extends a compatible map `α` whenever `hn` states that it
kills `m^(n+1)`: first factor through the actual quotient test using
`LocalAdicArtinianTests.factor`, then compose with the completion projection.
`restriction_extensionAt` proves the resulting restriction is exactly `α`.

`mapEquiv ε hε A` is the equivalence

```
Maps (augmentation ε hε) A ≃ Maps ε A.
```

Its forward map is exactly restriction, as `mapEquiv_apply` records.
`mapEquiv_naturality` proves that it commutes with every actual test arrow.
`mapEquiv_symm_eq_extensionAt` identifies its inverse with every permitted
finite-stage extension, so the extension does not depend on a chosen bound.
There is no separate continuity premise or restriction to selected test arrows.

## Implemented proof and internal provenance

The local ring, quotient evaluations and Cauchy-sequence congruences are the
actual Mathlib constructions. The private `factor_eval` follows their compatible
quotient equations. The private `ker_eval` compares the algebra evaluation with
the module evaluation through their canonical quotient algebra equivalence;
finite generation identifies the latter's kernel with the extended ideal power.
Mathlib's equality of the completion's maximal ideal with the extended original
maximal ideal gives `ker_projection`. Choosing a representative of a quotient
class then proves `exists_approximation`.

Surjectivity of restriction uses `LocalAdicArtinianTests.exists_bound`: every
compatible original map to an Artinian test kills some positive maximal-ideal
power, so `extensionAt` applies. For injectivity, the same bound theorem applies
to both maps from the actual local completion. Choose the larger bound and
approximate a completion element by an original element to that order. Both
maps kill the difference, and their restrictions agree on the original element.
Thus they agree on every element. This argument does not require a noetherian
premise on the completed ring for the bound theorem. `Equiv.ofBijective` packages
the comparison; associativity of actual algebra homomorphisms proves naturality.
All ingredients are internal algebra constructions and proved imported results;
no external representability assertion is invoked.

## Scope

This unit supplies an augmented complete local source and its full Artinian map
comparison. It does not construct a deformation hull, a formal Picard family, an
algebraization, or a smooth scheme atlas. Those geometric existence and comparison
obligations remain part of the surrounding Picard task.
