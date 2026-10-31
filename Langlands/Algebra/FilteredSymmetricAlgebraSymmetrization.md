# Filtered whole-algebra symmetrization

For a field `R : Type` and an arbitrary-universe Lie algebra `L : Type v`,
this internal construction compares the actual symmetric algebra with the
genuine enveloping algebra at each finite degree bound. No finite-dimensionality
assumption on `L` is made.

`envelopingWordSpan R L d` is the linear span of the ordered genuine generator
words indexed by lists of length at most `d`. The theorem
`degreeFiltration_eq_envelopingWordSpan` identifies it with the existing genuine
filtration `degreeFiltration R L d`, defined as the `d`th submodule power of
constants plus the generator image. For one inclusion, submodule-power induction
reduces multiplication to a scalar or a generator; the latter appends a letter
to a word. The reverse inclusion uses the existing word degree bound.

`symmetricDegreeFiltration R L d` is the linear span of the corresponding
products of actual symmetric-algebra generators. The two length-bound spans are
monotone. The published monomial formula for whole normalized symmetrization
and its degree bound extend by linear span induction to
`symmetricAlgebraSymmetrize_mem_degreeFiltration`. Thus
`symmetricAlgebraSymmetrizeDegree R L d` is the linear restriction from the
symmetric span to the genuine enveloping degree piece.

With the additional assumption `CharZero R`, `map_symmetricDegreeFiltration`
proves that the image of the symmetric span is exactly that genuine degree
piece. The reverse inclusion uses strong induction on the degree bound.
It suffices to lift an ordered word of length at most the bound. The empty word
is the image of one. For a nonempty word, symmetrizing its symmetric monomial
differs from the ordered word by an element of degree at most its length minus
one. The induction hypothesis lifts that difference within its smaller degree
bound, and monotonicity places this lift within the original bound. Subtracting
the lifted difference from the monomial image recovers the ordered word.

Consequently `symmetricAlgebraSymmetrizeDegree_surjective` proves surjectivity of
each restricted map, including degree zero.
`symmetricAlgebraSymmetrize_surjective` then uses the exhaustiveness of the
genuine enveloping filtration to prove surjectivity of the whole linear map.

The provenance is internal: the argument combines the existing genuine
submodule-power filtration, its word bounds and exhaustiveness, and the strict
characteristic-zero monomial comparison from
`SymmetricAlgebraEnvelopingSymmetrization`. It does not identify a homogeneous
grading, prove injectivity or a PBW isomorphism, assert multiplicativity of
symmetrization, or establish invariant lifting, central generation or the
automorphic differential-growth theorem.
