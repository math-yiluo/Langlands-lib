# Conjugacy recovered from an actual full geometric piece

This internal supporting construction assembles the last endpoint of the
uniqueness argument in Renard, *Représentations des groupes réductifs
p-adiques*, 9 July 2026 edition, VII.2.6 theorem, second proof paragraph,
printed p.231 / PDF p.237. After both intersection parabolics have been
proved full, their normalized Jacquet and induction functors reduce to
transport of the original representations. A nonzero intertwiner between
the resulting irreducible representations yields the desired conjugacy.

The input is an actual `GeometricLemmaIntersectionDatum D` from the
published represented geometric lemma. Its original group schemes,
parabolic, Levi and radical maps, multiplication witnesses, intersection
identities and conjugating isomorphism are retained. Both intersection
parabolic maps `D.p'` and `D.q'` must be isomorphisms. This file does not
prove their fullness or produce a nonzero map from a geometric filtration.

`D.fullLeviConjugacy` extends `D.φ` to an isomorphism between the two
original Levi group schemes. It reuses the published rational-Levi
construction and satisfies the literal ambient conjugacy equation with
the rational point `z⁻¹`. Its direction is from the inducing Levi `M` to
the Jacquet target Levi `L`, agreeing with the final VII.2.6 statement.

`D.fullLeviPointsEquiv` is the corresponding topological group equivalence,
formed from the two actual full-parabolic point equivalences and `D.e`.
The computation theorem proves that its forward map is exactly the
rational-point map of `D.fullLeviConjugacy`. The proof identifies the
inverse point maps with the maps of the inverse scheme isomorphisms.

`D.fullPieceEquiv` identifies `D.pieceFunctor.obj σ` with `σ` transported
along the inverse recovered point equivalence. Its linear map is
evaluation at the identity followed by the full Jacquet class-to-vector
equivalence. Equivariance follows successively from the actual normalized
induction and Jacquet equivalences. The point conjugation between the two
intersection Levis is the supplied `D.e`.

`FullPieceConjugacy` (in the intersection-datum namespace) stores the actual scheme isomorphism, its ambient
conjugacy equation, the linear equivalence and its intertwining law.
`D.fullPieceConjugacyOfNonzeroMap` constructs this data from irreducible
representations `σ` and `τ` and a nonzero intertwiner
`D.pieceFunctor.obj σ → τ`. Precomposing with the inverse piece
equivalence preserves nonzeroness. Pullback along the recovered group
equivalence preserves irreducibility: the proof explicitly identifies the
two lattices of invariant subspaces. Schur's nonzero-map alternative
therefore makes the transported map bijective. Evaluating its
intertwining law at the forward image of a point of `M` gives the exact
original-point law in the output record.

The field universe and the two representation-carrier universes are
independent. The construction uses the canonical ambient point topology,
the published Levi-point topologies, a Hausdorff topology on the field,
and the supplied locally compact and nonarchimedean ambient point group.
It requires no local-field, temperedness, square-integrability,
admissibility, central-character, quotient-compactness or standardness
hypothesis. It concerns the full geometric piece; comparison with the
unitary geometric piece, the geometric lemma, the two fullness arguments
and all three final VII.2.6 propositions remain separate obligations.
