# Actual finite Galois fields with split maximal tori

This internal construction packages published existence theorems into actual
data. The ground field is arbitrary, and its universe `u` is arbitrary.

For a group scheme `G` over `Spec k`, `FiniteGaloisSplitMaximalModel G`
contains a field `L : Type u`, a `k`-algebra structure, finite dimensionality
and Galoisness, a commutative group scheme `T` over `Spec L`, and an actual
homomorphism from `T` to the pullback `G_L`. It records that `T` is split and
that this homomorphism is a maximal torus. The imported maximality predicate
includes closedness and tests factorizations through every closed torus over
`L`. The conclusion therefore retains maximality among all field tori.

If `G` is smooth and affine over `k`,
`nonempty_finiteGaloisSplitMaximalModel` constructs the bundle. It applies the
published `exists_finiteGalois_hasSplitMaximalTorus` with
`torusFiniteGaloisSplitting` and `maximalTorusBaseChange`. This discharges both
structural hypotheses of that helper. Its proof first chooses a maximal torus
over the original field, splits that torus over a finite Galois extension,
and preserves maximality by the field-extension theorem. The present proof
unpacks the resulting witnesses into the bundle.
`finiteGaloisSplitMaximalModel` chooses such a bundle.

For any supplied bundle `D`, `D.fpqc` proves that the actual map
`Spec D.carrier → Spec k` is surjective, flat and quasi-compact, by the
published field-extension property theorem. `D.hasSplitMaximalTorus` supplies
the existing predicate using the bundle's torus and inclusion.
`D.isConnectedReductive` proves connected reductivity of `G_L` from that of
`G`, using the published ascent theorem along algebraic extensions. The
bundle's finite-dimensional field extension supplies algebraicity.

The provenance is internal. The module combines the published maximal-torus
existence, finite Galois splitting, maximality under field extension, fpqc
field-cover and algebraic-extension ascent interfaces. It introduces no new
structural assumption or restriction on the ground field. Its data can be
used as the finite splitting stage in the quasi-split inner-form construction.
It supplies no root datum, pinning, quasi-split ground-field model, adjoint
quotient, descent datum, or inner discrepancy; those remain separate
obligations of the inner-form existence target.
