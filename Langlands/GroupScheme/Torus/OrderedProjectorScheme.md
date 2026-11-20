# The affine scheme of ordered matrix projectors

An ordered family consists of pairwise orthogonal idempotent matrices indexed by a finite set, with sum the identity and with each projector nonzero at every residue field. The last condition says that the entries of each projector generate the unit ideal. The label and matrix index types may be empty.

`OrderedProjectorScheme.CoordinateRing` starts with the polynomial ring on the matrix entries and imposes orthogonality, idempotence and completeness. In this quotient the entry ideal of each universal projector is finitely generated and idempotent. The identity `P² = P` writes each generator as a sum of products of two entries. Mathlib's finitely generated idempotent ideal theorem supplies an idempotent generator. Equating this generator to one cuts out the locus where that projector has positive rank. These equations allow the positive ranks to vary across components.

`universal` is the family on the resulting ring. An ordered family over an algebra defines a polynomial evaluation which kills the matrix relations. The image of each idempotent generator generates the specialized entry ideal, so it is a unit and hence equals one. Thus evaluation factors through the final quotient. `homEquiv` proves uniqueness by the universal matrix entries.

`scheme` is the relative spectrum of this ring. `pointsEquiv` applies the relative global sections and spectrum adjunction to classify projector families over the global functions of any test scheme. `pointsEquiv_naturality` identifies pullback with entrywise pullback of those functions.

This internal construction provides ordered charts for the moduli of closed subtori of a general linear group. The projectors become the coefficients of the distinct weights of a split torus. The construction above depends only on matrix identities and the ideal criterion for a clopen locus.
