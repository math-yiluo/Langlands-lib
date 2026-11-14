# Integral bases from signed spanning weights

This internal algebraic prerequisite isolates the lattice argument for the weights
of a maximal split torus. It applies to any additive abelian group `L`, a set `T`
that generates it as an additive group, a finite set `P` of representatives such
that every element of `T` is zero or is equal up to sign to an element of `P`,
and a natural-number multiplicity function `d`.

`span_eq_top_of_signed_support` proves that `P` spans `L` over the integers.
Its proof places `T` in the additive subgroup of the integer span of `P` and
uses the hypothesis that the additive closure of `T` is the whole group.

`card_eq_finrank_and_multiplicity_eq_one` assumes that every multiplicity on `P`
is positive and their sum is at most `finrank ℤ L`. The rank of a span is at
most the number of its generators. Positivity gives the opposite chain

`finrank ℤ L ≤ P.card ≤ ∑ x ∈ P, d x ≤ finrank ℤ L`.

Equality throughout implies that the cardinality equals the rank, and equality
of the sums of `1` and `d` forces every multiplicity on `P` to be one.

`basisOfSignedSupport` then uses Mathlib's basis construction over a ring with the
Orzech property, here the integers. The resulting basis consists of the actual
elements of `P`, as recorded by `basisOfSignedSupport_apply`. `exists_fin_basis`
reindexes it by `Fin r` when the integral rank is `r` and retains both membership
in `P` and the multiplicity-one conclusion.

`eq_zero_of_basis_pairing` supplies the corresponding detection lemma: for an
integer bilinear pairing that separates the second argument, vanishing against
all elements of an integral basis in the first argument forces the second
argument to be zero. The proof uses the extensionality of linear maps on a basis.

The provenance is internal: this is an elementary consequence of generation,
the span rank bound, and the Orzech basis criterion already available in Mathlib.
No algebraic group theorem or field hypothesis is used. In the intended isometry
application, faithfulness supplies the generating support, and the geometry of
the quadratic form must supply the positive multiplicities and their bound.
This module does not prove those geometric hypotheses or the maximal-torus
weight statement itself.
