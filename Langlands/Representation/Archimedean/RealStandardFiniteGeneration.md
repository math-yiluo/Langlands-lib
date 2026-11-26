# Finite generation of real standard modules under matrix derivatives

For any list \(d\) of real blocks of total rank \(n\),
`realStandardFiniteGeneration` gives a finite-dimensional subspace of
the \(O(n)\)-finite standard module that generates the whole module
under words in right derivatives along real \(n\times n\) matrices.
Taking the complex span of those words is the usual generation over the
complex universal enveloping algebra.

In Langlands order, choose a vector outside the largest proper
\((\mathfrak g,K)\)-submodule supplied by `realLeviLanglandsQuotient`.
Its compact orbit spans a finite-dimensional subspace. The word span
of that subspace is stable under the compact and Lie actions and
contains the chosen vector, so the maximality property forces it to
equal the whole module.

For a finite filtration given by `IsFiltration`, suppose the source of
each filtration map has such a generating subspace. In the target take
the sum of their images. Its word span contains all ranges of the
filtration maps by induction on their index. Indeed, applying a matrix
derivative before or after the current map has a difference belonging
to the span of the earlier ranges. Those differences are already in
the target word span, so the preimage of that span under the current
map is stable under the derivatives and contains the generating
subspace of its source.

For arbitrary block lists, use the adjacent-character and adjacent-induced
filtrations at an inversion. Each piece has the same exponent support
up to permutation. A swap decreases the inversion count, and every
replacement strictly increases the squared-weight sum. That sum is
bounded by the fixed exponent support, so induction on the squared-weight
deficit and then the inversion count gives finite generation in all
orders.

This is an internal consequence of the Library's Langlands quotient and
filtration theorems. The enveloping-algebra convention for finite generation
is that of Wallach, *Real Reductive Groups I*, §3.3.2.
