# Fixed covariant functions on a supplied dense product cell

This internal derived construction concerns an affine group scheme `G` over
an arbitrary field `k : Type u`. An actual morphism `i : H → G` from an
affine group and an actual morphism `j : U → G` specify left covariance and
right invariance. The latter source need not be affine or unipotent, and
neither morphism is assumed injective. No external theorem is invoked.

`rightInvariantSubspace j` is the entire subspace of coordinate functions
with `f(g j(u)) = f(g)` on every original relative scheme test. Its submodule
laws follow from linearity of coordinate evaluation.
`pointAlgebraHom_one_apply` identifies evaluation at the identity point of
any test scheme with scalar extension of the coordinate counit.

`eq_of_pointAlgebraHom_eq_on_unit_locus` proves equality of coordinates that
agree at every point where a supplied nonzerodivisor `q` has unit value.
Apply the hypothesis to the point over the spectrum of each algebra
inverting `q`. The injective spectrum counit converts coordinate evaluation
to the algebra map. The existing localization separation lemma then gives
equality after multiplication by a power of `q`, and the nonzerodivisor
condition cancels that power. This argument needs neither reducedness,
algebraic closure nor rational-point density.

Now supply a factorization `g = i(b) j(u)` on every relative test whenever
`q(g)` is a unit, and a coordinate `d` that is left covariant of a supplied
weight `χ`, right invariant under `j`, and has counit one. The coordinate
`q` cutting out the test locus may differ from `d`; the weight need not
already be known to be a character.

`eq_counit_smul_of_covariant_rightInvariant` proves that every coordinate
`f` with the same covariance and invariance equals `(counit f) • d`.
At a product point, right invariance removes `j(u)` and left covariance
evaluates the remainder as `χ(b) f(1)`. Applying the same computation to
the normalized `d` proves the claimed equality on the unit locus.
Localization separation extends it to the entire coordinate algebra.

`leftCovariant_inf_rightInvariant_eq_span` identifies the intersection of
the entire left-covariant subspace and the entire right-invariant subspace
with `span k {d}`. One inclusion is the scalar-multiple theorem and the
other follows because `d` satisfies both conditions. No finite subspace is
substituted for either entire space, and no finite-dimensionality
hypothesis is used.

The factorization, the normalized covariant and its right invariance
remain supplied hypotheses. This module proves no existence of
structural big-cell data, Steinberg representations or cofinal
irreducibility, and it does not prove orbit spanning for any covariant
space.

Integration gives the local instances used here module-specific names to permit
joint imports. Their types, values, and local scopes are unchanged.
