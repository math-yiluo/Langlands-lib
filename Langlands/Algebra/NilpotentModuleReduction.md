# Endomorphism rigidity modulo a nilpotent base ideal

Worker 626. This internal algebraic construction works for a commutative ring
R and an arbitrary R-module M, with independent universes and no finiteness
assumptions.

`reduction I` is the ring homomorphism from the endomorphisms of M to the
endomorphisms of M / IM induced by quotienting each endomorphism. Every
endomorphism preserves IM by R-linearity. Its value on the class of x is the
class of f(x). The kernel consists exactly of maps whose image lies in IM.

`range_pow_le` proves by induction that if f(M) is contained in IM, then
the image of f^n lies in I^n M. The induction maps the previous image bound
through f, uses that linear maps preserve ideal scalar products, and applies
the bound on the image of f. Consequently f is nilpotent when I is nilpotent.

`eq_of_reduction_eq` proves that two commuting idempotent endomorphisms
with equal reductions modulo a nilpotent ideal are equal. Their difference
has image in IM and is therefore nilpotent; Mathlib's
`eq_of_isNilpotent_sub_of_isIdempotentElem_of_commute` then gives equality.
`eq_of_sub_mem` gives the same result from pointwise congruence modulo IM.

Commutation is an explicit hypothesis. These algebraic results are intended
for left and right character projections; this module makes no assertion
about group schemes or infinitesimal centrality.
