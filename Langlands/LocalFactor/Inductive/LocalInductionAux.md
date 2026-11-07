# Coordinates and spectral evaluation for actual local induction

This internal auxiliary construction specializes the published range comparison
and degree coordinates to the actual local Weil groups of p-adic fields. The
base field and extension field may occupy independent universes. The coefficient
field is `ℂ`, and the representation carrier occupies the extension field's
universe. The prime is arbitrary.

For a p-adic embedding `g : E →ₐ[Padic p] E'`, a finite-dimensional complex
representation `A` of `localWeilGroup E'`, and arbitrary elements `Φ`, `Φ'` of
degree one, `localInductionCoordinates` is a linear equivalence

```
(induceAlong (extensionWeilMap E E' g) A)^(localInertia E)
  ≃ₗ[ℂ] (Fin (extensionResidueDegree E E' g) →
    A^(localInertia E')).
```

The displayed expression abbreviates the actual invariant-space carriers in
Lean; induction uses the existing injectivity proof for `extensionWeilMap`.
The construction first uses `InductionAlong.invariantCoinductionEquiv`, which
preserves every value of the underlying equivariant function. It then applies
`InductionDegree.coordinates`. The existing identity
`localDegreeInt_extensionWeilMap` gives the required degree scaling, and
`extensionResidueDegree_pos` gives its positivity. Local inertia is the kernel
of the actual local degree homomorphism.

`localInductionCoordinates_apply` states that coordinate `i` is evaluation at
`Φ^(-i)`. The lemma `localInductionCoordinates_action_apply` identifies the
coordinate after the action of any `w : localWeilGroup E`: its value is the
original function evaluated at `Φ^(-i) * w`. Both formulas follow directly from
the definitions and their right-translation convention.

The remaining three lemmas concern the actual residue cardinalities.
`extensionResidueCardinality_log` derives `log q_E' = f * log q_E` from the
published identity `q_E' = q_E^f`, using the real logarithm followed by the
canonical inclusion in `ℂ`. `extensionSpectralParameter_pow` then proves

```
exp(-s * log q_E)^f = exp(-s * log q_E')
```

for every complex `s`, using the exponential's natural-power identity.
Finally, `extensionExpandedPolynomial_eval` combines that equality with
`Polynomial.expand_eval`, for an arbitrary polynomial over `ℂ`.

These are derived comparisons of existing Library constructions and Mathlib
identities; they introduce no new literature assertion. They use no continuity
assumption on the representation. This module supplies the local coordinate
and evaluation ingredients; the cyclic determinant calculation and the exact
`EulerFactorInductionStatement` proof are separate.
