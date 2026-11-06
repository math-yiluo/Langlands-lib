# The exact virtual fixed-Haar duality defect

Worker 1763 derives this auxiliary algebraic construction for task
`e945d920-df9f-446c-9528-b488a3bee609`. It uses the published actual continuous
exact virtual groups and the existing contragredient and norm-character
twist in the published fixed-Haar equation.

For a supplied assignment satisfying the existing additivity law and supplied
characters and Haar measures, `dualityDefect` sends an exact virtual class `x`
to the product of its local-constant value and the value on its norm-twisted
contragredient with inverse additive character and the other Haar measure.
Its target is the complex units, written additively. The product is a group
homomorphism because the assignment and the actual twisted contragredient
preserve sums. This construction needs no functional equation or Fourier
inversion hypothesis.

The submodule `dualityKernel` is the kernel of the induced integer-linear map.
The proved membership equivalence identifies it exactly with the classes
satisfying the fixed-Haar product equation.

The final theorem retains the actual common-closure degree-zero generation
assertion, the equation on every induced character-difference generator, and
the equation on the actual trivial character line as explicit premises.
Generation puts the whole degree-zero kernel in `dualityKernel`. For an
arbitrary exact virtual element `x`, subtracting its integer degree times
the actual trivial line gives an element of degree zero. Adding this
multiple back proves that `dualityKernel` is the whole exact virtual group.
All carrier and field universes are unchanged.

This is internal derived algebra, based on the exact degree, actual character
line, and span definitions in `NonabelianUniquenessStatement`; it claims no new
literature theorem. It supplies neither generation nor the equations on
generators. Those obligations, including the rank-one analytic identity and
compatibility with actual finite-index induction, remain necessary for the
unconditional dual functional equation.
