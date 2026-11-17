# Irreducible constituents of a coefficient span

`CoefficientSpanConstituentsStatement` is proved by `coefficientSpanConstituents`,
which applies `irreducibleSubquotient_of_coefficient_span`.

This internal supporting result is derived for the proof of the Variant in Renard,
*Représentations des groupes réductifs p-adiques*, version of 9 July 2026,
VI.10.7 (printed pp.215–217, PDF pp.221–223). It is a general algebraic lemma,
not a separately stated assertion of the source. It assumes no unproved
Bernstein characterization, no reductivity and no finiteness of the coefficient algebra.

Let `ρ` be a smooth representation over a commutative complex algebra `B`,
on a compatible complex vector space `V`. Let `S` be an actual subrepresentation
of its underlying complex representation. If the carrier of `S` spans `V` over
`B`, every irreducible actual subquotient of `V` is an actual subquotient of `S`.

Multiplication by `b : B` gives a complex intertwiner `S → V`.
The supremum of the invariant images of these intertwiners is all of `V`:
span induction proves that it contains every `B`-linear combination of elements
of `S`. The published theorem `SmoothRep.irreducibleSubquotient_iSup` locates an
irreducible subquotient in one such image, using a nonzero vector and the
finite support of membership in an invariant sum. That image is an actual
quotient of `S`; published transitivity of actual subquotients finishes the proof.

In particular, predicates on irreducible constituents, including membership of
their Bernstein inertial supports in a fixed finite set, pass from `S` to `V`.
This lemma alone does not prove the family finite-type characterization.
