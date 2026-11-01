# Adjacent-rank compact-section spanning

This is an internal consequence of the published compact-average construction,
exact ordered lower-parabolic geometry, and compact local-section spanning
proof. It uses no additional literature theorem or analytic convergence premise.
The field is an arbitrary Hausdorff topological field. Its universe and that of
the original algebraic complex module are independent; every natural rank,
including zero, is retained.

Write `P` for the opposite parabolic of `adjacentRankLowerShape r`, `a` for its
actual large-block projection, and `tau` for
`adjacentRankCompactSectionRepresentation P a rho xi adjacentRankUnitCharacter`.
The last character is the explicit trivial smooth character. The measure is
finite on compact sets and the inner character's complex values are locally
constant. The given representation is smooth; its carrier has no topology or
norm. For the section construction the measure must also be preserved by every
right multiplication by `a(q)`. The earlier covariance theorem uses precisely
this hypothesis.

`adjacentRankLowerSectionTensor` specializes the existing bilinear tensor map
to this actual lower parabolic. It allows any outer smooth character; the
spanning results in this file concern the trivial outer character.

For a compact open subgroup `J`, the frame-orbit indicator is the admissible
compact test from `AdjacentRankFrameOrbit`. If `v` is fixed by `P` intersected
with `J`, acting through `tau`, then
`adjacentRankFrameSlice_integrand` identifies its inner integrand at identity
with the constant vector `v` on the slice `a(P intersect J)` and zero elsewhere.
Indeed, a slice element is `a(q)` for `q` in `P intersect J`; applying fixedness
to `q` inverse gives the factor `xi(h) rho(h inverse) v = v`.
`adjacentRankFrameSlice_average` uses the finite algebraic indicator integral
to get `c v`, where `c` is the real mass of that slice, embedded in the complex
scalars. The slice is compact open and contains identity. Thus, if the measure
is positive on nonempty open sets, `adjacentRankFrameSlice_mass_ne_zero`
proves `c` is nonzero and finite.

`adjacentRankFrameOrbit_section` proves equality of actual smooth induced
functions between the orbit section and `c` times the standard compact
double-coset section centered at identity with value `v`. On `P J`, covariance,
whole-`J` right invariance of the test and the identity average give the value.
Off `P J`, the exact frame-orbit criterion makes the whole inner integrand
zero, while the standard section's projected-support theorem makes that
section zero as well. No injectivity of a scalar coefficient map is used.

`adjacentRankFrameOrbit_translate_mem_range` divides by `c` and uses the
published right-translation law to place every right translate of each such
compact local section in the range of the tensor map. Finally,
`adjacentRankCompactSectionTensor_covers_compact` applies the existing
`compactLocalSectionSpanning` theorem, using a supplied compact open subgroup
basis. The range is a submodule and contains all of those generators, so it
contains every compactly induced vector after the canonical inclusion into
smooth induction. The actual opposite parabolic's closedness is discharged
by its published closedness theorem.

This file does not assert that the whole smooth induction is compact,
surjectivity for arbitrary outer character, normalized tensor-carrier
surjectivity, any Jacquet integral identity, a common nonzero Whittaker
functional, or the host model-image theorem. Those remain further steps.
