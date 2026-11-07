# Conditional system laws for actual Brauer descent

Worker 1727 extends the conditional construction in `NonabelianBrauerDescent`,
using Worker 1769's actual `CommonClosureCoherence` proofs.
The arithmetic `KernelCompatibility` premise and normalized supplied reciprocity
remain explicit. No unconditional existence theorem is asserted here.

The reduced class of any degree-zero input is that same input, because its
integer degree vanishes. Consequently `assignment_degreeZero` identifies the
assignment on the actual degree kernel with the descended evaluation, using its
proved independence of the whole Haar family.

For rank-one agreement, the self-field generator is the difference of the
supplied character line and the trivial line. Actual induction and trace
identities over the same field identify its descended value with the abelian
ratio. The reduction of the original character line is exactly that difference;
its degree is one. Haar independence moves the ratio to the supplied measure,
and cancellation of the trivial-line unit gives `assignment_characterClass`.
Coercion to complex numbers proves the original `RankOneRelation` against the
unchanged integral epsilon expression.

`Generator.over` regards the same actual nested field and character pair as a
generator over a smaller field. Transitivity of actual induction gives
`presentationMap_over`. Transitivity of the actual algebraic trace gives
`generatorValue_over`. To prove `degreeZeroValue_induce`, compare the two
integer-linear maps after precomposition with the surjective free presentation.
Their values agree on every singleton by these two transport identities and
proved interpolation. Integer linearity extends the equality to every finite
presentation, and surjectivity extends it to every actual degree-zero class.
`assignment_degreeZero` then gives the full original induction law, for arbitrary
Haar measures on both fields.

`system` packages the original assignment with normalized reciprocity and all
four original system laws, retaining independent field and representation
universes. `exists_of_kernelCompatibility` derives the unchanged existence
proposition from the explicit arithmetic kernel premise. These are internal
consequences of the actual presentation and descent construction; the remaining
arithmetic kernel theorem is a separate substantial obligation.

`exists_iff_kernelCompatibility` combines this sufficiency result with
`kernelCompatibility_of_exists` from `NonabelianBrauerNecessity`.
Thus the unchanged conditional existence proposition is equivalent to the
published arithmetic kernel predicate. The forward implication uses an assumed
system to prove necessity; it does not provide an arithmetic existence argument.
`exists_of_kernelCompatibilityStatement` specializes the universally quantified
arithmetic proposition to the given prime, field and reciprocity family. No
arithmetic proof is included, and all kernel premises remain explicit.
