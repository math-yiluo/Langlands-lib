# Compatible Reynolds projections and finite covariants

Author: Worker 94.

This internal algebraic construction isolates the final finite-covariant
argument in Harish-Chandra, *Representations of a semisimple Lie group on a
Banach space I* (1953), proof of Theorem 1, part 2.3, printed page 200 /
one-based PDF page 16. The registered original is
`provided-3653f29ecd116fbb8becf37a078787d768f76f5b4bc4b075c85b5b9647628636`,
retained at
`/home/taskhub/pilot/literature/Harish-Chandra, Representations of a semisimple Lie group on a Banach space I, Trans. AMS 75 (1953).pdf`.
The pair gives an abstract projection formulation of that elementary
reduction, rather than a statement of Harish-Chandra's full theorem.

Let `A` be a commutative coefficient ring, `S` an `A`-algebra, and `M`
an `S`-module equipped also with an `A`-module structure. For an `A`-submodule
`W` of `M`, `ReynoldsPair A S M W` consists of an `A`-linear coefficient
map from `S` to `A` and an `A`-linear retraction from `M` onto `W`. The
compatibility law says that projecting `s • w` for `w` in `W` gives
the projected coefficient times `w`. The definition requires exactly
these maps and identities. It asserts neither their existence nor that
`A` and `W` are fixed points of any particular group or Lie action.

`ReynoldsPair.moduleFinite` proves that `W` is finite over `A` whenever
the ambient module `M` is Noetherian over `S`. The implemented proof
first takes the `S`-span of all vectors of `W`. Noetherianity supplies a
finite subset of `W` generating this span over `S`. For these same
vectors, let `T` be their `A`-span. Additive span induction and the
compatibility law show that projection of the full `S`-span lands in
`T`. The retraction fixes each vector of `W`, so `W` is contained in
`T`. The reverse inclusion holds because the chosen generators belong
to `W`. Thus the same finite set generates `W` over `A`.
No scalar-tower hypothesis on the two module structures is required;
the displayed compatibility law for the projections suffices.

`ReynoldsPair.moduleFinite_of_noetherianRing` specializes the result to
a finite `S`-module over a Noetherian ring `S`. No Noetherian hypothesis
on `A` is used.

In the source's application, `S` is the polynomial algebra on the
Cartan complement, `A` is its compact-Lie invariant subalgebra, and
`W` is the invariant part of a polynomial module tensored with a
finite-dimensional representation. Semisimple decompositions supply
the two compatible projections there. This pair does not construct
those projections for the actual number-field matrix Lie algebra.
PBW and filtered transfer, finite generation over restrictions of
ambient invariants, reductive central directions, and the actual
compact-group type comparison remain separate obligations. No actual
central covering, admissibility, analyticity, reproduction or
automorphic differential growth follows from this pair alone.
