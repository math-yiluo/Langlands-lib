# Local units for actual smooth Hecke actions

For a Hausdorff locally compact totally disconnected topological group with its
Borel measurable structure and a Haar measure, the actual integrated Hecke action
on a smooth complex representation has normalized compact-open local units.
The group and representation carrier have independent universes. The carrier
has only an additive commutative group and complex module structure, with no
topology, norm, finite-dimensionality or completeness assumption.

`exists_normalizedIndicator_fixes` gives a compact open subgroup whose normalized
indicator fixes a prescribed vector. Smoothness first provides an open subgroup
fixing that vector. Applying `TestFunction.commonCompactOpenBiInvariance` to the
empty family of test functions and that subgroup gives a compact open subgroup
contained in it. The intrinsic normalized-indicator formula from
`ActionProjection` then fixes the vector.

`exists_normalizedIndicator_fixes_finset` gives a single such indicator for a
finite family of vectors. Finite-set induction begins with compact-open
refinement of the whole group. At each insertion it refines the intersection of
the previous compact open subgroup and an open stabilizer of the new vector.
Previously fixed vectors belong to the previous fixed subspace by the range
property of the normalized operator, so the smaller subgroup fixes them too.
The empty vector family is included.

`heckeAction_nondegenerate` says that a vector annihilated by every actual Hecke
operator is zero. Apply the annihilation hypothesis to a normalized indicator
that fixes the vector. These results use no additional `NonarchimedeanGroup`
assumption: the imported common-invariance proof derives the needed compact-open
refinement from the stated topological hypotheses.

This is an internal consequence of the integrated action and common-invariance
construction, motivated by the natural Hecke module in Flath, section 1,
printed page 179 (`flath-1979-tensor-products`). The proofs above describe the
implemented argument rather than a proof quoted from Flath.

The common-invariance proof and normalized indicator are published imports.
The local-unit laws are intrinsic consequences of the fixed-vector projection
constructed in the companion `ActionProjection` module.
