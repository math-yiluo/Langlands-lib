# The residue-coordinate comparison of Drinfeld and Deligne points

Drinfel'd, *Coverings of p-adic symmetric regions* (1976), §2A, printed p. 109 (PDF p. 3), gives the height-zero framed triples and the basic theorem identifying their functor with the unramified base extension of Deligne's formal scheme. Section 2B, printed p. 110 (PDF p. 4), gives the division uniformizer relations and the graded module construction underlying the comparison.

`HasDrinfeldCyclicRelations` records the relations used here. A division unit has `d`-th power the scalar uniformizer. It conjugates the chosen embedded unramified field by an automorphism acting on its integral elements modulo the maximal ideal by the residue-cardinality power. The special framing module supplies the unramified subfield condition, the dimension, and height `d²`. The residue field for the frame is an algebraic closure of the local residue field with the compatible scalar tower.

`DrinfeldDeligneResidueComparisonStatement` asserts a natural isomorphism of the two actual functors on affine `Nilp` algebras over the integer ring of `K`. The source is the Library's height-zero framed comparison-class functor. The target pairs actual admissible Deligne classes with the actual maps of the residue extension into `B/(π)`. At every test algebra the isomorphism recovers the original residue map as its second coordinate.

The proposition targets the underlying comparison in residue coordinates. The action correspondence and the identification of residue maps with maps from the completed unramified coefficient ring are separate obligations.
