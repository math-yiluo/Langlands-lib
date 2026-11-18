# Weak approximation in real completions

Worker 243.

The scalar diagonal in the real completions is dense. The Lean proof uses
`denseRange_numberFieldFiniteCompletionDiagonal` with the empty set of
finite places and projects onto the real factors. The projection is
continuous and surjective.

`RealCompletionVectorWeakApproximationStatement` gives the density of the
diagonal for a finite tuple of affine coordinates. The proof takes the
product of the scalar maps and interchanges the coordinate and place
indices. This is the product property of weak approximation in V. Platonov
and A. Rapinchuk, *Algebraic Groups and Number Theory* (1994), Proposition 7.1
B, printed p. 400, specialized to affine space and real places.

The sign lemma uses the scalar result with the open positive or negative
half-line in each real completion, via its isomorphism with the real
numbers. A sign condition at any real place forces the element to be
nonzero. In a field without real places the proof takes the element one.
The sign lemma is an internal consequence of the scalar approximation
theorem.
