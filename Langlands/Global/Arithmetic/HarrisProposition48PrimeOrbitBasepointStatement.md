# Arithmetic basepoint of the prime Mackey orbit

Harris (1998), Proposition 4.8, printed pp. 202–203, uses a basepoint of the
prime-sized Mackey orbit and compares its Galois conjugates at the unique place
over the auxiliary place. The formal basepoint is the representative `1` of the
double-coset quotient. The carrier fields of the supplied child and the
corresponding intermediate fields of the parent can be different Lean types.

`Proposition48Problem.IsPrimeOrbitBasepoint` records the two ring isomorphisms from
the child's fields to the parent's base intermediate field and identity
compositum. They commute with the base embeddings. The actual child character
is the pullback along the inducing-field isomorphism, and transport along the
base-field isomorphism sends the child's auxiliary place to the displayed
place over the parent's auxiliary place.

`Proposition48PrimeOrbitBasepointStatement` extracts these same isomorphisms
from `IsAuxiliaryMackeyChild D 1`. In that witness the transported auxiliary
place already lies over the parent's place, so uniqueness identifies it with
the displayed place. The relation ties subsequent arithmetic and local
automorphic comparisons to this chosen child.
