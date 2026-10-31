# Actual conjugation on enveloping degree pieces

This internal construction combines the published actual archimedean adjoint
automorphisms with the published enveloping degree filtration and the generic
filtered-map lemma. It is valid for every field `K : Type u` and every natural
rank. The final orbit-finiteness result additionally assumes `NumberField K`.

`envelopingConjugation_mem_degreeFiltration` uses the actual generator identity
for `envelopingConjugation`: a generator is sent to the generator of its actual
complexified matrix conjugate. The generic filtered-map lemma therefore proves
preservation of every degree piece. Applying the same argument to the inverse
gives the membership equivalence.

`envelopingDegreeConjugation` is the resulting complex linear equivalence of
each degree piece. The identity, multiplication, and inverse laws are
restrictions of the existing actual adjoint laws. They define
`envelopingDegreeRepresentation`, an algebraic representation of the entire
archimedean group, including its disconnected components.

`envelopingConjugationOrbitSpan` is the linear span of the actual full-group
conjugates of one enveloping element. Any degree piece containing that element
contains this entire span. Exhaustivity and the finite-dimensional degree
pieces over a number field then give
`envelopingConjugationOrbitSpan_finite`.

No topology or continuity assertion is made for these representations. This
unit supplies algebraic compatibility of actual conjugation and filtration;
symmetrization, enveloping central generation, admissibility, and the final
automorphic differential-growth theorem remain further obligations.
