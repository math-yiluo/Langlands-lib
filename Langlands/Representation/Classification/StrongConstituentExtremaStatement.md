# Strong irreducible constituents from lattice extrema

Author: Worker 502.

`Langlands.Classification.StrongConstituentExtremaStatement` is an internal
algebraic statement over every group `G : Type uG` and every complex
representation on a carrier `V : Type uV`. The two universes are independent.
It states two equivalences:

1. There is exactly one coatom in the actual subrepresentation lattice if and
   only if the canonical quotient `head ρ` satisfies `IsIrreducibleHead ρ`.
2. There is exactly one atom in that lattice if and only if the canonical
   restriction `socleRepresentation ρ` satisfies `IsIrreducibleSocle ρ`.

The head relation requires an actual surjective intertwiner and equality of
the kernels of all irreducible quotient maps. The socle relation requires an
actual injective intertwiner and equality of the images of all irreducible
embeddings. The competing irreducible representations have carrier universe
`uV`, exactly as in the existing relations. The statement concerns equality
of actual subrepresentations, not only isomorphism classes.

The canonical head is the quotient by the intersection of the kernels of
irreducible quotient maps. The canonical socle is the restriction to the sum
of the images of irreducible embeddings. These are the constructions in
`CanonicalConstituents`; this statement introduces no choice of constituent.
There is no finite length, finite dimension, topology, smoothness,
admissibility, or nonzero hypothesis. In particular, the statement does not
assert existence of an atom or a coatom for an arbitrary representation.
For the zero representation both existence assertions and their corresponding
irreducibility assertions are false.

This is a derived interface motivated by the lattice conclusion of Zelevinsky,
*Induced representations of reductive p-adic groups II* (1980), Proposition
2.10, printed p.180/PDF p.17. Its precise formulation uses the Library's
canonical constructions and strong constituent relations; it is not a
transcription of a representation theorem from that source. An independent
proof should use the correspondence between irreducible quotients and coatom
kernels, and between irreducible embeddings and atom images. The source's
segment, Jacquet-module, and orientation arguments are separate obligations.

The sole import is `CanonicalConstituents`. No segment or multisegment
classification conclusion, analytic classification, or contragredient argument
is an assumption of this statement. A smooth application uses the existing
`SmoothRep.headQuotient` and `SmoothRep.socleSubrepresentation`, whose
underlying representations are the two canonical constructions here.

This module supplies a proposition definition only. It contains no proof of
the two equivalences or of a segment constituent existence theorem.
