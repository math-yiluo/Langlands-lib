# Irreducible constituents from separating intertwiners

`Langlands.HasSeparatingIntertwiners ρ σ` says that for every nonzero
vector of `ρ` there is an intertwiner to `σ` whose value on that vector
is nonzero.

Suppose `ρ` is smooth and `σ` is admissible and Artinian over the complex
group algebra. Choose a vector with nonzero image under the given map
`q` from `ρ`. Evaluation at this vector injects the space of maps from its
cyclic orbit span to `σ` into the fixed vectors of an open subgroup of
`σ`. Admissibility makes this fixed space finite-dimensional. A basis
of the intertwiner space therefore gives finitely many maps separating
the cyclic orbit. The restrictions of the given separating intertwiners
ensure the separation property on that orbit.

Intersect the kernels of these maps successively. At the first step
where the image under `q` becomes zero, the preceding image is nonzero
and is a quotient of a subrepresentation of `σ`. This follows by
factoring `q` through the range of the map whose kernel is used at that
step. The preceding image is then Artinian and contains a simple
submodule. Pulling back that submodule gives a surjective intertwiner
from a subrepresentation of `σ` to an irreducible subrepresentation of
the target of `q`.

This is a derived algebraic argument for the finite-place extraction in
Task 6823. Langlands uses the finite length of the local induced
representations when identifying constituents in Lemma 1 of *On the
notion of an automorphic representation*, Corvallis Part I (1979),
printed p. 203 (PDF p. 198), source
`langlands-1979-notion-automorphic-representation`. The argument here
uses finite length through its Artinian consequence at one place at a time.
