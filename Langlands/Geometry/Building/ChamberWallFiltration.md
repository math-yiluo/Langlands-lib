# Root filtrations away from a chamber wall

This derived module compares actual root filtrations on a chamber and its
image under a chamber-simple coroot reflection. Its two multiplicative
equivalences preserve the underlying rational point. The result supports
the geometric part of chamber-simple factorization.

## Setting and conclusions

The generic sign theorem works on an arbitrary real affine torsor with
`IsAffineRootSystemWithRankZero Ψ`. Let `C` be a chamber, `ψ` a simple
affine root for `C`, and `v` a coroot for `ψ`. For a root `eta ∈ Ψ`,
assume that `eta.linear` is not a real scalar multiple of `ψ.linear`.
Then `sign_eq_simpleReflection_of_linear_not_proportional` proves that
`eta` has the same sign at every `x ∈ C` and at the reflection of `x`
through the wall of `ψ` using `v`.

The apartment comparison uses an arbitrary universe-`u` field `k`, the
existing affine group-scheme embedding `i`, a function `ω : kˣ → ℝ`, and
actual `D : KPApartmentData i ω`. It assumes:

- `IsAffineRootSystemWithRankZero D.affineRoots`;
- apartment AS4, explicitly that each extended affine root or its double
  belongs to `D.affineRoots`;
- a chamber `C`, a simple affine root `ψ` for `C`, and a coroot `v` for `ψ`;
- an actual relative root `a` such that `rootForm i a` is not a real scalar
  multiple of `ψ.linear`.

Write `s` for the actual affine reflection `affineReflection ψ hv.1`.
The point comparison
`filtration_eq_simpleReflection_of_not_proportional` proves, for every
`x ∈ C`, both equalities

```text
D.filtration x a 0     = D.filtration (s x) a 0
D.filtrationPlus x a 0 = D.filtrationPlus (s x) a 0.
```

The theorem `rootFixer_eq_simpleReflection_of_not_proportional` then proves
both equalities

```text
D.rootFixer a C     = D.rootFixer a (s '' C)
D.rootFixerPlus a C = D.rootFixerPlus a (s '' C).
```

The entry `rootFixerEquivSimpleReflection_of_not_proportional` and the
companion `rootFixerPlusEquivSimpleReflection_of_not_proportional` are
`MulEquiv.subgroupCongr` applied to those subgroup equalities. Both
directions preserve the ambient rational point; the two forward coercion
lemmas make that behavior explicit. The subgroups are the existing
valuation-defined root fixers in `rationalPoints G`.

## Implemented proof

For the generic sign theorem, a chamber point is regular for every affine
root. Its reflected image is also regular, because the coroot reflection
preserves the root system. The published chamber-wall comparison makes
this chamber-simple reflection the unique root reflection separating the
two points. If `eta` changed sign, its own coroot reflection would be such
a separating reflection and hence would equal `s`. The existing
`hyperplane_le_of_affineReflection_eq` and
`eq_smul_of_hyperplane_le` then make `eta` a scalar multiple of `ψ`.
Taking linear parts contradicts the hypothesis. The nonzero values
therefore have positive product and equal sign.

The theorem
`sign_eq_extendedAffineRoot_simpleReflection_of_not_proportional`
uses AS4 to replace any extended affine root of derivative `rootForm i a`
by itself or its positive double. A positive scalar multiple still has
derivative not proportional to `ψ.linear`, and positive scaling preserves
sign, so the generic sign theorem applies.

For an actual root element other than the identity, the published
`exists_extendedAffineRoot_of_ne_one` gives an extended affine root
realizing its finite valuation at every apartment point. The preceding
sign equality preserves both nonnegative and strictly positive
valuation membership. The identity has valuation top at both points.
Extensionality of the actual filtration subgroups gives the two point
equalities. Finally, the published root-fixer membership formulas express
membership by the corresponding filtration condition at every chamber
point. Reindexing these conditions through the image `s '' C` gives the
two root-fixer equalities and hence the identity equivalences.

## Provenance and scope

The content is derived entirely from the current Library
`AffineChamberWallComparisonProof` and `ChamberFiltration` modules,
their imported affine-reflection and valuation interfaces, and Mathlib's
subgroup congruence equivalence. No new external-source assertion is
introduced.

The result requires no rank-one factorization, cover comparison, or
ordered-product premise. It addresses directions away from the wall.
The exceptional proportional direction and the full chamber-simple
factorization remain open, as does the apartment-only
`AffineIwahoriTitsStatement`. No hypothesis of that published target is
changed or discharged by this intermediate unit.
