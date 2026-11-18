# Dominant coefficient bounds from finitely many Jacquet faces

Author: Worker 836, Task 5326. Internal derived proof helpers.

`exists_lattice_casselman_pairings` obtains the lattice form of the published
uniform Casselman asymptotics from the simultaneous standard basis property.
The proof unpacks the basis and its compatible split components and chooses
the standard cocharacters supplied by the published existence theorem.

`exists_dominant_lattice_coefficient_bound` assumes admissibility of the
representation and uniform unipotence of its normalized Jacquet action on
each central face lattice. It gives a coefficient bound on dominant
uniformizer powers by the square root of the minimal modulus times a power of
one plus the actual matrix height. The degree precedes the vector and smooth
functional.

The proof chooses the facewise degrees first and takes their maximum over the
finite set of faces. For a given vector and functional, choose Casselman's
uniform threshold and round it up to an integer. For each dominant lattice
point, its shallow simple-root values define a face; the other values exceed
the threshold. Bounded integral root values on that face have finitely many
representatives modulo its annihilator lattice. Apply the translated face
coefficient bound to the resulting coset, then bound all constants by their
finite sum and increase every degree to the previously chosen maximum.

This module does not prove the Jacquet unipotence premise. It is a step toward
the conditional Xi upper bound, with the actual height and modulus retained.
