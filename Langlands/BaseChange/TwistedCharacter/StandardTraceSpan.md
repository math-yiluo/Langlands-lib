# Spanning twisted irreducible traces by stable standard traces

For an ordered tempered Langlands datum with stable blocks, twist each
block by its real determinant character and induce its twisting
isomorphism. The determinant character is invariant under the entrywise
field automorphism. The resulting operator is the Library's normalized
induced σ-intertwiner on the actual standard module.

`StableLanglandsTraceSpanStatement` says that every twisted distribution
of a stable irreducible admissible representation of positive-rank
\(GL_n\) over a \(p\)-adic field `E` belongs to every subspace that
contains these standard traces. Here `σ` is an `F`-algebra automorphism
of `E` with the supplied `F`-module topology. The representations and
standard data use carrier universe `max v z` for `E` in `Type v`. The
measure is left-invariant and finite on compact sets.

Choose a stable ordered Langlands presentation for the irreducible.
The ordinary multisegment order strictly decreases on irreducible
subquotients of the head kernel. Well-founded induction puts their
twisted traces in the subspace. Exactness of twisted traces across the
preserved head kernel gives the irreducible head trace for the supplied
twisting isomorphism.

This is the distribution form of the stable standard-module spanning
argument of Henniart–Lemaire (2011), II.5.10. The proof uses ordinary
composition multiplicities for descent and actual twisting operators
for additivity.
