# Affine multiplicative-type quotients of closed diagonalizable inclusions

This internal construction produces actual affine fppf quotients of closed
inclusions between diagonalizable group schemes over an arbitrary ring.
It is derived from the explicit exact quotient, local character
surjections for closed inclusions, fppf quotient gluing, and relative
multiplicative-type locality.

`isFppfQuotient_exactQuotientMap_arbitraryRing` removes the Noetherian and
nonzero restrictions from the exact quotient associated with a supplied
surjective character map. The actual map over `R` is identified, through
the canonical diagonalizable base-change isomorphisms, with the base
change of the integral quotient. Flatness, surjectivity and local finite
presentation transport through these isomorphisms. The full kernel
equality was already proved over every coefficient ring.

`exists_quotient_of_closed_inclusion` applies to a closed inclusion
`f : D_R(Γ) ⟶ D_R(Λ)` when `Λ` is finitely generated. It gives a group
of multiplicative type `Q` and an affine homomorphism `D_R(Λ) ⟶ Q`
which is the actual fppf quotient by the full range of `f`.
The definition `closedQuotient` chooses such a quotient while retaining
these proofs. The original ring may have nilpotents or zero divisors,
and neither character group is required to be torsion-free.

The proof uses the actual open restriction cover of `f`, with its proved
surjective character map on each member. The exact quotient of the
corresponding character map, base-changed to that open member, supplies
a local quotient. The subgroup condition is identified with `f` by
the retained actual local morphism equality. The explicit local
quotient targets are diagonalizable and hence of multiplicative type.
The source diagonalizable group is commutative, so the subgroup is normal.

The supporting theorem `exists_quotient_of_local_quotients` glues supplied
affine multiplicative-type quotients on any fppf base cover. Quotient
comparison identifies the base change of the global target with each
local target. Fppf locality then proves multiplicative type of the global
target. Its projection is affine because the original source is affine
over the base and the quotient target is affine and separated over the
base.

This module treats closed inclusions whose two groups are already given
by diagonalizable models over a ring. Passing from arbitrary groups of
multiplicative type to these local models remains a further step.
