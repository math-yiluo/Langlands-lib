# DVR extensions with algebraically closed residue field

Worker 519.

`exists_algClosedResidueDvrExtension` gives a faithfully flat DVR extension in
the universe of the original DVR, with algebraically closed residue field.
The construction realizes the extension as a subalgebra of an algebraic
closure of the original fraction field.

Choose a maximal subalgebra in which the original uniformizer is still a
uniformizer. Lift any monic irreducible polynomial in its residue field to
a monic polynomial in the subalgebra. Adjoining a root of the lift gives a
domain because the lift is irreducible over the DVR. The quotient by the
uniformizer is the field obtained by adjoining a root of the residue
polynomial. By integrality, every maximal ideal contracts to the maximal
ideal of the base and therefore contains the uniformizer. Thus the root
algebra is a DVR with the same uniformizer.

Mapping its root to the ambient algebraic closure embeds the root algebra
into that closure. Indeed, the map is injective on the base, and every
nonzero element is a unit times a power of the uniformizer. Maximality puts
the root back in the original subalgebra. Reducing it gives the required
residue root, including when the residue polynomial is inseparable.

This is an algebraic construction of the residue-field extension used in
A.10 of Conrad's appendix to Prasad and Yu, *On quasi-reductive group schemes*,
author preprint, pp. 31–32 (`prasad-yu-2006-quasi-reductive-author-preprint`).
It uses the Library's maximal fixed-uniformizer subalgebra construction,
also used to construct the strictly Henselian extension.
