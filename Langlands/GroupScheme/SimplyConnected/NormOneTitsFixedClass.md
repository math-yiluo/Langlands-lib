# Actual fixed-algebra Brauer representatives for the norm-one conventions

The actual norm-one chart matrices satisfy the column intertwining
equation on every test scheme. Applying the inverse-transpose group
automorphism to that equation gives `dualConjugator_normOneChartPoints`.
The scalar maps commute with inverse transpose, so the formula uses the
same field-level dual conjugator on every test algebra.

For a Galois splitting field, `transpose_mem_oppositeFixed_iff` transports
membership in the two actual fixed algebras via the transpose
equivalence. `mem_oppositeFixed_iff_dualConjugator` computes the defining
equations of the opposite fixed algebra. Transposing the original equation
and cancelling the invertible conjugator gives the dual equation.

`fixedCSA` equips the actual fixed matrix algebra with its central,
simple and finite-dimensional structure using `fixedEquivOfIsGalois`.
Its matrix-stable Brauer class is the class of the original algebra.
For the transpose chart, the representative is the fixed algebra of
the actual opposite algebra, whose class is the additive inverse in
the published Brauer quotient.

This internal deduction uses the norm-one chart equations, arbitrary
Galois fixed-algebra recovery, inverse transpose and the published
Brauer class of the multiplicative opposite. It applies in every
characteristic with fields and the input CSA in the same arbitrary
universe. The calculation concerns the fixed representatives attached
to the charts. The comparison with the general additive Tits obstruction
requires identification with its highest-weight representation algebra.
