# Renard IV.1.5 from completeness of irreducible Hecke actions

Author: Worker 142. Module
`Langlands.Representation.CompactCoefficient.CompactProjectionDistributionReduction`,
namespace `Langlands.Renard.CompactRepresentation`.

The module defines the internal predicate
`ProjectionDistribution.IsProjector`, exactly the local action predicate in
`CompactProjectionDistributionStatement`. It also proves the conditional theorem
`compactProjectionDistribution_of_heckeCompleteness` with independent universes
`u` and `v`:

```lean
HeckeCompletenessStatement.{u, v} → CompactProjectionDistributionStatement.{u, v}
```

This is a reduction, not a proof of the premise or an unconditional proof of the
task's target. The only retained premise is the already published completeness
statement, Renard III.1.11. The target statement and all its imported files are
unchanged.

## Implemented proof

Completeness applied to the difference of two Hecke elements proves that equality
of their actions on all irreducibles implies equality of the elements. Integration
commutes with intertwiners, so an actual representation equivalence transports
equality of actions. Consequently it suffices to compare actions on `τ` and on
irreducibles inequivalent to `τ`. This proves `unique` from the two defining
projector properties.

For `K' ≤ K`, evaluate each of `e' * e`, `e_K * e'`, and `e' * e_K` on the
irreducibles. On `τ` the equalities are the published normalized-indicator
convolution identities. On an inequivalent irreducible they are zero. This
proves `refinement` under completeness.

The conjugation argument does not use completeness. Scalarize the integrated
action by arbitrary algebraic dual functionals. Right invariance of the Haar
measure gives the right-translation formula
`π(R_g f) v = π(f) (π(g⁻¹) v)`. Together with the published left-translation
formula, this gives
`π(x ↦ f(g⁻¹ x g)) = π(g) π(f) π(g⁻¹)`.
The same left and right measure invariances preserve the mass of a conjugate
compact open subgroup. Its normalized indicator is therefore the conjugate of
`e_K`. These facts prove `isProjector_conjugate` with precisely the conjugation
convention in the target, without introducing a modular factor.

Finally, use the unconditional `exists_element` from
`CompactProjectionDistributionConstruction` for existence, `unique` for
uniqueness, and the refinement and conjugation lemmas for the remaining two
clauses. The resulting conditional theorem has no premises beyond
`HeckeCompletenessStatement`.

## Provenance and scope

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026, IV.1.5, Theorem and proof, printed p.92 / PDF p.98.
Registered source ID `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
This page was read in the retained original. The uniqueness and refinement
arguments follow its completeness argument. Existence uses the Library's
intrinsic compact-isotypic splitting, as documented in the companion
construction module, rather than Renard's formal-degree formula. The
right-translation and normalized-indicator conjugation calculations are
internal derivations from the published integration and Haar invariance APIs.
