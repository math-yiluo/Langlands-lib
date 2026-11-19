# Eisenstein functional equation on a regular parameter patch

`Langlands.Global.EisensteinFunctionalEquationRegularComparisonStatement`
uses the group, parabolic, compact subgroup and automorphic data of
`EisensteinFunctionalEquationStatement`. It takes the same scalar
meromorphic continuation `EP` of the `P`-series and the same finite family
`∑ i, coeff i λ • ψ i` representing the continuation of the intertwining
operator. For every bound `R` it asks for one nonempty open patch in
linear coordinates on the parameter space of `P`. At every parameter
`λ` of that patch the Weyl image `wλ` must be `R`-regular for `Q`, and at
every adelic point `g` the equality on the patch is

`EP λ g = ∑ i, coeff i λ * E_Q(ψ i, wλ) g`.

Here `E_Q` is the actual series `hK'.eisensteinSeries`, evaluated in a
region chosen sufficiently far inside the regular chamber for `Q`.
The statement allows `R` to be enlarged to accommodate finitely many
convergence or agreement thresholds. It includes the empty family.

This comparison is a derived formulation of the initial equality in the
proof of Bernstein–Lapid, *On the meromorphic continuation of Eisenstein
series*, Theorem 2.3 (4), §8.6. Their proof identifies the two families
there by equality of leading cuspidal components, using §6. Applying
their comparison to the universal continuation data here requires
uniqueness of those scalar continuations from the initial regular
region of `P`.

`Langlands.Global.EisensteinFunctionalEquationRegularComparisonReductionStatement`
asserts that this comparison implies the published functional equation.
The intended deduction selects `R` large enough for all supplied
continuations on the `Q` side to agree with their series on the patch.
The scalar meromorphic identity principle then extends the equality to
the common holomorphy domain.
