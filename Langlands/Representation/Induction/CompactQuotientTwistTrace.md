# Finite character expansions for induction from a compact quotient

This is a derived consequence of the actual fixed-vector and trace
constructions in `Representation/Induction/FiniteTwistTrace`. It adds no
original-literature assertion. Group, coefficient, parameter and second
coefficient universes are independent.

Let `P` be a closed subgroup of a Hausdorff, locally compact, totally
disconnected topological group `G`, with compact actual left quotient
`P \ G`. The measurable structure is Borel, and the measure is left
invariant and finite on compact sets. Let `sigma` be an admissible complex
representation of `P`. Admissibility has the Library's all-open-subgroups
meaning: smoothness and finite-dimensional fixed vectors for every open
subgroup.

For every actual Schwartz--Bruhat test function `f`,
`exists_induced_distribution_twistCoefficients` produces a single
finitely supported complex function `c` on `P`. It is chosen before any
character. For every character `chi : P -> complex units` trivial on all
compact subgroups of `P`, and every proof of admissibility of the actual
twisted smooth induction, the actual distribution character evaluated at
`f` is

`sum (p in support c), c(p) * chi(p)`.

The definition `compactQuotientTwistCoefficients` chooses this `c` from
the proved existence theorem. Its arguments contain no character or
induced-admissibility proof. The intrinsic law
`compactQuotientTwistCoefficients_eval` gives the displayed formula for
that same chosen function for every allowed character.

The test function's common compact-open bi-invariance follows from
`Hecke.TestFunction.commonCompactOpenBiInvariance`, applied to its singleton
family. Compactness of the quotient gives a finite double-coset
transversal by `exists_finset_doubleCoset_representatives`. Every component
of its evaluation model is the `sigma`-fixed subspace for the open
subgroup `conjOpenSubgroup P K i`, so admissibility supplies a finite
dimensional component. The finite product therefore has a finite basis,
chosen by `Module.finBasis`. Neither the transversal nor the basis is an
extra input to this result.

The stabilizers are compact by `isCompact_conjOpenSubgroup`: this uses
closedness of `P` and compactness of `K`. The character condition makes
each stabilizer act trivially through `chi`. The theorem
`induced_distribution_eq_twistCoefficients` then proves the displayed
formula using the genuine twisted induction and integrated Hecke action.
The admissibility of that induced representation remains explicit; this
result does not infer it from a finite-dimensional model at just one
level.

For a parameter space `A`, let `chi(a)` be such compact-trivial subgroup
characters with each scalar evaluation `a |-> chi(a)(p)` continuous.
Assume actual admissibility of every twisted induction.
`continuous_induced_distribution_twist` proves continuity of its
distribution value at each fixed test function. The proof rewrites the
value by the same chosen finitely supported function `c` for all parameters,
and uses continuity of a finite sum of the scalar evaluations.

Finally, `induced_distribution_twist_eq_of_dense` compares two such
families, possibly from different closed subgroups and on carriers in
different universes. Equality of their actual distribution characters on
a dense subset implies equality for every parameter. For each test
function, the equality locus of the two continuous scalar functions is
closed and contains the dense subset, so it is the whole space.

These results provide a continuity and extension step. The dense subset,
the character families and their evaluation continuity, coefficient and
induced admissibility, and equality on that dense subset are explicit
inputs. In particular, no generic same-Levi equality, unramified-character
realization, reductive admissibility theorem or exact finite-length K0
Weyl-conjugacy theorem is asserted here. Classification, character
independence, the geometric lemma, adjointness and cuspidal support do not
occur in this proof route.
