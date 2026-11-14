# Compatible full integral coordinates for a root datum

This internal supporting construction chooses coordinates on both entire lattices of an integral root datum. It does not construct a group scheme or assert any integral existence theorem.

For a root datum `P` on abelian groups `X` and `Y` and a finite basis `B` of `X` over the integers, `dualCoordinates P B` identifies `Y` with integer coordinate vectors using the perfect pairing of the root datum. Its coordinate at `i` is the pairing of `B i` with the given coweight. The equivalence is the composite of the perfect-pairing identification with the dual lattice and coordinates in the dual basis.

`ofBasis P B` transports the whole datum using the weight coordinates of `B` and these dual coweight coordinates. `ofBasisEquiv` is a full root-pairing equivalence. The proof of `pairing_eq_sum` expands a weight in the basis and uses bilinearity; applying this to the inverse coordinate maps proves `ofBasis_pairing`, the standard integer dot product. The root and coroot formulas follow from the transport definition. Reducedness follows by transporting linear independence along the weight equivalence and then applying reducedness of the original datum.

`exists_equiv_standard` requires finite generation of `X` and reducedness of `P`. The existing theorem that the weight lattice of a root datum is torsion-free, together with the finite module hypotheses over the integers, supplies a finite free basis. Applying the preceding constructions gives a finite coordinate type, a reduced full coordinate root datum and a full equivalence with the original datum, with standard pairing. No root-spanning or semisimplicity condition is used, and the construction retains central directions and permits empty root-index and coordinate types.

The provenance is internal linear algebra: Mathlib's perfect-pairing equivalence, dual basis and root-pairing transport, and the Library's `rootPairingMapEquiv` and `isTorsionFree_weight`. This addresses the coordinate choice required by `ChevalleyIntegralExistenceStatement`; the actual integral group, torus inclusion, reductivity and fibre realizations remain separate obligations.
