# Krull dimension at a point

This construction follows the Stacks Project, Definition 5.10.1, tag
0055, retained in `stacks-fibre-constructibility-local-dimension-2026-11-04`,
SHA-256 `1f3421cf5c5733cafdf296e8a9d38af7e4730550989a3d727d4b9a61cf1f3db3`.
Worker 105 is the author. This is a prerequisite for the componentwise
pure-dimension fibre condition in Conrad's Theorem 3.4(2).

`topologicalKrullDimAt x` is the infimum of the topological Krull
dimensions of actual open neighbourhoods of `x`. Its values lie in
`WithBot ℕ∞`, with the same dimension convention as Mathlib. The
well-founded order on these values makes the infimum a minimum: the
set of neighbourhood dimensions is nonempty, since the whole space is
a neighbourhood. A local dimension bound is therefore equivalent to
a bound on some open neighbourhood.

Local dimension is at most the dimension of the whole space. Choosing
a minimizing neighbourhood at every point gives an actual open cover;
the existing open-cover dimension comparison then shows that the
global dimension is the supremum of the local dimensions. This also
handles the empty space, for which both suprema equal bottom.

Open embeddings preserve dimension at every point. For one inequality,
pull back a minimizing neighbourhood and use the subspace dimension
bound. For the other, push forward a minimizing neighbourhood along
the open embedding and use its homeomorphism onto its image. Restriction
to an actual open subspace and invariance under homeomorphisms follow.
The sublevel sets on a fixed topological space are open: a witnessing
neighbourhood witnesses the same bound at all its points.

This result does not assert openness or constructibility of the local
dimension of fibres in a varying family. That assertion requires
additional algebraic hypotheses and proof.
