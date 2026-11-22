# Geometric Frobenius and completion embeddings

This module supplies the local restriction step for quadratic Frobenius
patching. Restriction along the Library's chosen closure embedding commutes with
that embedding. For two successive field embeddings, restriction along the
composite of the chosen closure embeddings agrees with the iterated
restriction. The Library's change-of-closure intertwiner then compares it
with restriction along the closure embedding chosen for the composite field
map. Applying this to both paths through the square of field and completion
embeddings gives `completionSquareEquiv`. [Closure restriction](../ClosureRestriction.md)

The chosen closure embedding for an algebraic field extension is bijective.
Its absolute restriction has image the pointwise fixing subgroup of the copy
of the larger field transported back through the closure isomorphism. The proof
conjugates a fixing automorphism through the isomorphism to construct its
preimage. When the original field map is surjective, the transported copy is
the embedded base field and the absolute restriction is surjective.

If the base map preserves and reflects the valuation unit ball, the chosen
closure embedding carries spectral integers to spectral integers by
integrality. It carries elements of spectral norm strictly less than one to
elements of spectral norm strictly less than one as well. For such an element
`x`, a power of `x` divided by a fixed nonzero base element of norm less than
one is integral. Transporting that relation gives the strict inequality in the
target closure. Applying the strict inequality to inverses then shows
reflection of integrality. Bijectivity gives the isomorphisms of spectral
integer rings and their residue fields. The residue isomorphism intertwines
the two Galois actions by checking on representatives in the integer rings.

The residue comparison identifies upstairs inertia with the preimage of
downstairs inertia. If the residue cardinalities satisfy \(q_w=q_v^d\), the
inverse of a geometric lift at \(w\) acts on the residue closure by
\(x\mapsto x^{q_w}\). This is the action of the \(d\)-th power of the inverse
of a geometric lift at \(v\). Inverting the residue actions proves
`residueAction_map_eq_pow`. In the unramified representation, two elements
with the same residue action act by the same endomorphism. The completion
square therefore gives unramifiedness of the pullback and computes its
Euler polynomial from the \(d\)-th power of an actual geometric lift at \(v\).
[Frobenius lifts](../FrobeniusLift.md)

When the completion map is surjective, every downstairs inertia element lifts
to upstairs inertia. For equal residue cardinalities the exponent above is one.
These two facts descend `HasEulerPolynomialAt` through a completion isomorphism.
An intertwining equivalence also preserves `HasEulerPolynomialAt`, by
conjugation of the inertia and Frobenius actions after localization.
