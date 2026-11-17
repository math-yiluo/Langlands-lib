# Fppf torus conjugation aligning actual root restrictions

This internal derived construction compares two supplied families of root power
formulas over a commutative ring. The target roots have independent integral
exponent vectors. Both formulas use the same source and target root maps and
the same powers, and their scalar coefficients are units.

For coefficient families `c` and `c'`, `rootAlignmentUnits` takes their ratios
`c / c'` into the global units of a test scheme. `rootAlignmentLift` applies the
independent monomial lifting theorem to these values. It gives a flat,
surjective, locally finitely presented cover and a point of the coordinate
target torus. `rootAlignmentLift_charValue` computes its root character values
on every refinement of that cover.

The target root parametrization's actual equivariance law then proves
`rootPoint_eq_conjugate_of_charValue`: the first root map is the conjugate of
the second by this target torus point. The scalar calculation is
`(c / c') c' x^q = c x^q`. `rootAlignmentLift_rootPoint` gives simultaneous
alignment on every refinement and global parameter; `exists_fppf_root_alignment`
packages the cover, torus point, and all these equations. This generic step
requires no local-ring, field, reductivity, finiteness, or positivity assumption.
The all-test power formulas and actual target parametrizations are explicit
inputs.

The construction is derived from the published independent-exponent character
lifting theorem and the definition of an actual root parametrization. It uses
character naturality and pullback of base scalars, followed by equivariance and
the unit identity above. Thus equality is proved on all scheme tests over the
whole ring, including nonreduced rings and tests.

The actual-map adapters `RelativeIsogeny.exists_fppf_selected_root_alignment`
and `exists_fppf_simple_root_alignment` specialize this construction to two
finite homomorphisms between affine group schemes over a local ring. The two
maps have the same supplied coordinate torus map and root-datum isogeny
`r : RootDatumIsogeny p Q P`, with the explicit actual-character compatibility.
The target is reductive, its coordinate torus is fibrewise maximal, and both
reduced root data are supplied fibrewise root data of the actual groups.
Source and target root parametrizations are supplied for each selected target
root and its corresponding source root. The selected target roots are linearly
independent; the simple-root specialization obtains this independence from a
supplied base of `Q`.

For each selected root, the preceding finite-root restriction theorem
constructs a unit coefficient and proves the formula on every scheme test,
with exponent `r.rootFactor`. Applying it to both maps supplies all inputs to
the generic alignment theorem. Neither the existence of the root-datum
isogeny nor equality of the homomorphisms on opposite roots or the whole group
is asserted here. These remain separate inputs and subsequent obligations in
the full rigidity proof.
