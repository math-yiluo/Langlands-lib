# The all-unit case of scalar standard rational descent

`allUnitStandardRationalGluing` proves the exact
`AllUnitStandardRationalGluingStatement`. For a positive-length tuple it
uses the actual finite pairwise-ratio Laurent refinement constructed in
`AllUnitLaurentRefinement`. Its point-independent index map and actual
inclusions choose a standard rational domain containing each leaf.

The retained refinement index is a subtype of Boolean choices with the
proposition that the tuple length is positive. An explicit equivalence
forgets that proof and identifies it with all Boolean choices. Reindexing
the proved iterated Laurent descent gives descent of this refinement.
Reindexing the universal version gives its descent after every bounded base
change.

The proof then applies the formal `ScalarCoverDescent.of_refinement`
theorem. It supplies both required premises: descent of the actual
refinement and separation of its pullback to every original standard
quotient. The latter follows from the universal refinement descent, using
the actual standard base map and the implication from unique lifting to
separation. Thus no analytic refinement-descent hypothesis is assumed.

For the empty tuple the absence of a common spectrum zero forces the
actual base algebra to be subsingleton. The scalar `0` is the unique lift of
the empty section family. No index of `Fin 0` is selected.

The source motivation is the all-unit case of Achinger's proof of Theorem
7.0.1, p.67, in the retained November 22, 2020 original identified in the
statement Markdown. The Lean implementation uses proved actual refinements,
universal scalar Laurent descent, and a formal descent transfer with local
separation. Worker 105 authored the all-unit refinement; Worker 84 the
iterated cover construction; Worker 101 the formal reindexing transport;
Worker 146 the compatibility preparation; Worker 572 this adapter and the
iterated descent proof.

The argument permits trivial scalar valuations, zero and nonreduced bases,
and empty rational loci. It proves scalar degree-zero descent for the
all-unit case at unit radii, with no assertion of higher exactness,
admissibility, finite-module descent, arbitrary radii or the arbitrary
nonunit standard case.
