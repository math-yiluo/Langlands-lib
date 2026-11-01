# Actual section exact sequences on integral schemes

`IntegralAmpleSectionCokernelStatement` records the first exact sequence
needed for dimension induction on ample Euler characteristics. All
sheaves, section morphisms, cokernels and stalk supports are the actual
published constructions.

On an integral scheme, a section of a module sheaf which generates on
a nonempty open gives a short exact sequence
`0 → O_X → M → cokernel(sectionHom M s) → 0`.
Its cokernel is zero exactly when the section generates on the whole
scheme, and its stalk support is contained in the closed complement of
the generation open. The coefficient sheaf need not itself be a line
bundle for this assertion.

The second assertion applies this to a positive tensor power of an
ample line bundle on a proper integral field scheme with positive
topological Krull dimension. For every point there is a section whose
generation open is affine and contains the point, and whose actual
cokernel is nonzero and supported in the complement of that open.

This is derived preparation for the regular-section argument in
Stacks Project, registered source
`stacks-numerical-intersections-finite-locally-free-rank-2026-10-31`,
`0BEL.html`, proof of Lemma 33.45.9. It uses the published generation-open
definition of ampleness. The statement expresses regularity as a
monomorphism in the actual sheaf category. It does not construct a
Cartier divisor scheme, prove a dimension formula for the cokernel
support, or claim an Euler polynomial or its leading-coefficient
positivity.
