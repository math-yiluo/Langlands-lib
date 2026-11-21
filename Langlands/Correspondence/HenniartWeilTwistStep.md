# The rank-wise twisting equivalence given scalar descent

`WeilScalarGradeDescent K e he l` specifies the remaining descent input: for a continuous irreducible representation whose upper group at `l` acts by scalars and whose groups at every larger real index act trivially, the scalar action is given by a character of the actual quotient `U_K^l / U_K^(l+1)` through geometric reciprocity. This module does not prove that input.

`weilSwanBelow_stepEquiv` uses it at `l > 0` in rank `k+1 = p^i`. The source is the product of the graded character group and the torsion-one orbits with natural Swan exponent strictly below `(k+1) * l`. The target is the torsion-one orbits of the same rank with natural Swan exponent at most `(k+1) * l`. Both are unramified-twist orbits of continuous irreducible Weil classes over the actual field. The field and carrier universes are independent.

## Implemented proof

The comparison of the natural Swan exponent with rank times the last break identifies the source's orbit bound with triviality at the upper group of index `l`. Integrality of the Swan exponent identifies the target bound with last break at most `l`, or equivalently triviality at every real index strictly larger than `l`.

For a graded character and a shallow orbit, take a representative of the orbit and twist by the chosen lift of the character. Twisting commutes with unramified twisting and preserves the unramified stabilizer. Its restriction at `l` is the prescribed scalar, and it is trivial on the deeper groups. If two resulting orbits coincide, the unramified twist relating them is trivial on inertia. An intertwiner therefore identifies their scalar multipliers on the upper group at `l`. Reciprocity onto the grade gives equality of the two character parameters. Cancelling their common lift then identifies their shallow orbits.

Conversely, a bounded orbit has scalar action at `l` by the positive-upper-bound lemma, using the torsion-one inertia criterion and the prime-power rank. The descent premise gives a graded character for that action. Twisting by the inverse of its lift kills the upper action at `l` and gives the required shallow orbit. Twisting forward recovers the original orbit regardless of the chosen representative of that shallow orbit, by commutation with unramified twists.

`weilConductorCountStep_of_scalarGradeDescent` applies the equivalence at every divisor rank of `p^r` and uses the extended-cardinality counting reduction and the size of the dual of the grade. It concludes the desired equality at the specified bound subject to the descent premise. No finiteness of the orbit sets is assumed.

## Provenance

This is the twisting and counting step of Guy Henniart, *La conjecture de Langlands locale numérique pour GL(n)*, Ann. Sci. École Norm. Sup. (4) 21 (1988), Proposition 3.3 and §3.4, pp. 508–509 (registered source `henniart-1988-numerical`), also described in Proposition `prop:H33` and Corollary `cor:14` of the 16 November 2026 operator route note. The equivalence uses chosen lifts as in §3.4; it does not require a group action of the unit-grade dual. The unconditional conductor-count theorem still needs the descent input.
