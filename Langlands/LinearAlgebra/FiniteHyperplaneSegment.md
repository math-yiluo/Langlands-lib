# Generic rational segments in finite hyperplane arrangements

This internal linear algebra helper is developed for the rational-parabolic
gallery proof in Task 5515. It concerns finite families of rational linear
forms on any rational vector space and has no group-scheme assumptions.

`Regular f x` means that all the forms are nonzero at `x`.
`SameChamber f x y` means that their values at `x` and `y` have positive
product. The determinant form based at `x` is `f(x)g - g(x)f`.
The segment is `(1-t)x + ty`.

The proof first uses Mathlib's finite proper-submodule avoidance theorem to
choose a vector where every specified nonzero form is nonzero. Adding this
vector to a sufficiently large positive rational multiple of a specified
endpoint preserves all its nonzero signs while resolving its zero values.
The explicit bound is one plus the sum of the absolute evaluation ratios.
Apply this construction to the original forms and all nonzero determinant
forms to choose a regular endpoint in the original chamber where the
nonzero determinants do not vanish.

Forms with equal strict endpoint signs never vanish along the closed
segment, by positivity of a convex combination. At a simultaneous crossing,
the determinant evaluates to zero by eliminating the segment parameter.
The endpoint choice therefore forces that determinant to be the zero form.
Evaluating that equality at an arbitrary vector shows that one form is the
other multiplied by the ratio of their nonzero starting values. The final
existence theorem combines these facts: a regular endpoint in the specified
chamber gives a segment with only one proportional class at each crossing.
These are proved linear facts only; the construction of actual dynamic
parabolics, maximal rank-one walls and the finite gallery is still separate.

The definitions and proofs are internal derived content. Their provenance is
the elementary finite-hyperplane argument described above, implemented using
Mathlib's `Module.Dual.exists_forall_ne_zero_of_forall_exists`.
