# Noetherian models with an actual section

This internal supporting unit constructs a finite type model over a finitely
generated ℤ-subalgebra of the affine base ring. The model includes the
actual flat, quasi-compact, quasi-separated, locally finitely presented structure
morphism and an actual section satisfying the section equation. Its Cartesian
comparison recovers the original morphism, and its section comparison recovers
the original section. The base ring and schemes lie in an arbitrary universe.

`NoetherianSectionModel` packages these data; its subalgebra is Noetherian because
it is finitely generated over the integers. `nonempty_noetherianSectionModel`
constructs such a model for every morphism and section satisfying the stated
hypotheses. The model does not assert geometric reducedness, and this unit does
not assert openness of the relative component subset.

The proof uses the already published Anthropic FLT scheme-descent, flat-descent,
and morphism-descent theorems. It first descends the scheme, enlarges the finite
stage to descend flatness, and then descends the section as a morphism from the
pullback of the identity on the finite-stage base. The morphism-descent theorem
retains the equation over the base, which gives the finite-stage section
equation. Its comparison identities give the actual section comparison. All
remaining morphism properties persist by base change.

The composition and Cartesian factorization helpers, and the restriction-of-
scalars packaging, adapt the implementation of the published Anthropic FLT
proper-flat triple descent proof
`S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_isPullback_comp_eq_of_isProper_of_flat_of_locallyOfFinitePresentation`.
This proof instead descends only the one morphism and its section and requires
no properness. To preserve arbitrary universes, it first works over the image
of the integers inside the original base ring, then restricts scalars to the
integers. Attribution for the imported FLT material is recorded in the imported
modules, `licenses/Anthropic-FLT/LICENSE`, `NOTICE`, and `ATTRIBUTION.md`.

The provenance is internal: this is the finite-stage descent construction
needed for the unrestricted-base section-component openness argument, derived
from the published descent inputs rather than an independently cited theorem.
