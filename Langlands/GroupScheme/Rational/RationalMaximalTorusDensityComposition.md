# The density deduction from the maximal-torus parameter propositions

`RationalMaximalTorusDensityCompositionStatement` is the implication from
`MaximalTorusParameterExistenceStatement` and
`MaximalTorusParameterUnirationalStatement` to the unchanged
`RationalMaximalTorusConjugateDensityStatement`, at arbitrary universe `u`.
The first premise supplies an actual parameter scheme and its projection for
each maximal ground-field torus. The second premise gives unirationality of
that same scheme, using its full `IsMaximalTorusParameter` predicate.

The theorem
`rationalMaximalTorusConjugateDensity_of_parameter_statements` implements
the implication. For an infinite field, smooth connected affine group and
maximal ground-field torus, it first chooses `Q`, `q` and their parameter
properties from the existence premise. Stability of smoothness under base
change gives smoothness of the actual pullback of `q` to the algebraic
closure. This supplies local finite type and openness of that map.

The unirationality premise applies to exactly this `Q` and `q`.
`IsUnirational.hasDenseRationalPoints` then gives ordinary ground-field
rational density in `Q`. The published
`hasDenseGeometricRationalPoints_of_hasDenseRationalPoints` extends those
actual ground-field sections to the algebraic closure and proves their
density there. Finally, `dense_torusConjugators_of_parameters` applies to
the open pullback map, the parameter's full conjugation compatibility and
this geometric density. Its conclusion is precisely the union of images
of the conjugators in the target proposition. In particular, it retains
actual closed ground-field tori and equality of subgroup functors on all
scheme tests. `rationalMaximalTorusDensityComposition` proves the packaged
conditional proposition by the same theorem.

This is an internal deduction from the imported Library statements,
definitions and proved density lemmas, together with Mathlib's smooth
base-change and openness results. It asserts no new correspondence with
external literature. It does not supply proofs of either parameter
premise, and it is not an unconditional proof of the task's density
target. That proof still requires the two unrestricted parameter
propositions to be proved.
