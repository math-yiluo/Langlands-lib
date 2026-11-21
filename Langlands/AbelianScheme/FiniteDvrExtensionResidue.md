# Residue fields of finite local DVR extensions

`FiniteDvrExtension.residueAlgebra` gives the residue-field algebra
induced by the supplied local map. To prove its algebraicity, lift a
residue element to the upstairs ring and use algebraicity in the
fraction-field extension. The primitive part of a polynomial over
the downstairs DVR still vanishes at the lift. Its reduction is
nonzero, since a zero reduction would make every coefficient
divisible by a uniformizer, contrary to primitivity. Reducing the
evaluation identity gives a polynomial relation for the original
residue element.

The residue extension preserves characteristic zero and algebraic
closedness of the base residue field. In a local ring with residue
characteristic zero, every positive integer maps to a nonzero
element of the residue field, so it is a unit. These facts supply
the residue and torsion-unit comparisons in the local monodromy
argument. The proof uses the Library's actual fraction-field tower
and local residue maps.
