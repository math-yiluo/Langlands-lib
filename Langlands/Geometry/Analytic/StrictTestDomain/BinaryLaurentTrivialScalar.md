# The actual binary Laurent amalgam over trivially normed scalars

Author: Worker 572.

This derived construction treats scalar degree-zero descent for the binary
unit-radius Laurent cover over a presented strict affinoid base `P` when
`∀ c : K, ‖c‖ ≤ 1`. It uses the published
`trivialScalarRationalLocalization` theorem, with the local `Algebra`
instances induced by the actual bounded structural maps. It leaves the
unconditional `BinaryLaurentGluingStatement` and all of its imports unchanged.

The upper denominator is `1`. Mathlib's `IsLocalization.atUnits` therefore
shows that its actual base map is bijective. The lower denominator is `f`,
and the actual four-variable overlap denominator is `1 * f = f`. Mathlib's
`IsLocalization.bijective` applies to the actual restriction from the lower
quotient to that overlap because `Inclusion.restriction_comp_baseMap` proves
that it commutes with the two structural maps from `P`. No replacement
quotient or unspecified comparison map is used.

`trivialScalarLaurentAmalgam` chooses the inverse image in `P` of an upper
section under the bijective upper base map. Its upper restriction equation
is the choice specification. For a compatible lower section, the two
structural-map identities identify the image of its proposed lower
restriction in the overlap with the left restriction of the given upper
section. Compatibility and injectivity of the actual right restriction
then prove the lower equation. Injectivity of the upper base map proves
uniqueness, recorded by `binaryLaurentGluing_of_trivialScalar`.

This is an internal algebraic consequence of the published localization
theorem and Mathlib's uniqueness of localizations. No further analytic
source result is used. The proof does not require a nonzero or reduced
base, a nonnilpotent `f`, or a nonempty lower or overlap locus. Localization
at a denominator that forces the zero ring is allowed. This contribution
constructs only the trivial-scalar branch; it does not prove the
unconditional binary statement, higher Cech exactness, admissibility,
arbitrary-radius descent, or descent for finite modules.
