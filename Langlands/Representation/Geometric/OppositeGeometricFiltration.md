# A composed opposite filtration from the upper geometric lemma

Worker 514 gives an internal conditional construction. Its input is a proof
of the existing `GeometricLemmaTheorem T B C.reverse` and one actual smooth
representation `A` of the inducing Levi `B`. For any refinement `S` of `C`,
the output is a finite filtration of the actual composed opposite Jacquet
module along `C,S` of the actual normalized upper induction of `A`.

`ComposedOppositeGeometricFiltrationData` retains the standard source and
target intersection refinements, their concrete intersection equalities, and
an enumeration of all minimal representatives for `B,C.reverse`. It also
records the constructed filtration and an actual equivalence for each grade.
That equivalence identifies the grade with the normalized refined opposite
Jacquet module of the original upper geometric piece pulled back along
`leviReverseEquiv C`. It does not simplify that quotient to an opposite
geometric piece.

`composedOppositeGeometricFiltrationOfUpper` unpacks the supplied upper
geometric lemma. Its permutation of the ordered filtration is composed with
the lemma's enumeration, so every representative is retained exactly once.
Evaluating the natural filtration at `A` gives actual invariant subspaces and
successive quotients. Evaluating its natural graded isomorphisms gives actual
representation equivalences. The construction then applies
`composedOppositeFiltrationOfReverse` and
`composedOppositeFiltrationOfReverseGradeCongr`. Smoothness of the ambient
induction follows from the published smoothness of normalized parabolic
induction.

The provenance is internal evaluation and composition of the existing upper
geometric-lemma interface and the actual opposite filtration adapters. The
field and inducing carrier universes remain independent; the induced and
Jacquet carriers retain their maxima. No geometric lemma is proved here:
the supplied proof of the upper geometric lemma is a required input.

The output still uses the reversed upper indexing and unsimplified actual
refined quotients. There is no claim identifying the coarse Weyl
contribution, selecting a responsible branch, or continuing a fixed branch.
This construction adds no premise to the supported branch obstruction and
does not prove that exact target.
