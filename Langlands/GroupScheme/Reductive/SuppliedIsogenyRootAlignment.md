# Fppf alignment of supplied root restrictions over arbitrary rings

This internal derived construction aligns two finite homomorphisms on a
supplied family of root coordinates over an arbitrary commutative ring `R`.
The source and target are affine group schemes with coordinate split tori.
Reduced root data `P` and `Q` are supplied as full fibrewise root data of
these actual groups. A root-datum isogeny `r : RootDatumIsogeny p Q P`
and an actual coordinate torus map are supplied, compatible on every
integral exponent character. Both homomorphisms have this same torus map.
The target is reductive and its coordinate torus is fibrewise maximal.

For a finite family `beta` of target roots, source and target additive
parametrizations of the corresponding actual root subgroups are explicit
inputs. The target root characters in this family must be linearly
independent over `ℤ`. There is no local-ring, nontriviality, or
reducedness assumption on `R`, and no decidable-equality assumption on
the torus coordinate types.

`SuppliedRootIsogeny.selectedRootAlignmentLift` constructs an fppf cover
of any test scheme `V` and a point of the target coordinate torus on that
cover. It applies the previously proved independent-character lift to
the ratios of the two maps' unit root coefficients. These coefficients
come from `SuppliedIsogenyRootUnit`; they are coefficients of the actual
represented root restrictions. The lift therefore supplies a flat,
surjective, locally finitely presented projection.

`selectedRootAlignmentLift_rootPoint` proves that this torus point
conjugates the second homomorphism to the first on every selected root
point over every scheme refining the cover. Both root restrictions have
the same prescribed exponent `r.rootFactor (beta a)`. Their all-test
unit-coefficient power formulas, together with actual target root
equivariance, give the equality: the character of the lifted torus point
is the ratio of the two coefficients, which scales the second
coefficient to the first.

`exists_fppf_selected_root_alignment` packages a cover, its torus point,
and these equations for every refinement and every global parameter.
`exists_fppf_simple_root_alignment` specializes the construction to the
support of a supplied base of `Q`, using the base's root independence.
The argument applies to arbitrary scheme tests, including nonreduced
tests and the zero-ring case.

The derivation reuses the arbitrary-ring generic construction in
`RelativeIsogenyRootAlignment` and the arbitrary-ring actual restriction
formulas in `SuppliedIsogenyRootUnit`. It preserves the existing
local-ring `RelativeIsogeny` API. Existence of the supplied root data
and parametrizations, comparison on opposite roots, and equality on
the whole group remain separate obligations in the full rigidity proof.
