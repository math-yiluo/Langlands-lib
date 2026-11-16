# Smoothness of the fixed integral Chevalley closure

This internal construction equips each field-valued base point with the
ordered negative-root, full character-torus and positive-root parameter
scheme, named `fieldOrderedCellSpace`. The root lists may be arbitrary.
Zero root coordinates and the torus identity supply a point over the
field. This part follows Worker 704's field-cell nonemptiness construction,
generalized from a ring map to any field-valued scheme point.

When the root index is finite and the character lattice is finitely
generated, the parameter scheme is smooth over any commutative base ring.
Each root parameter scheme is the spectrum of a polynomial algebra in
finitely many variables. The root-datum perfect pairing makes the
character lattice torsion-free, hence free over the integers; choosing a
basis identifies its diagonalizable group with a finite split torus.
Binary products preserve smoothness, as does field base change.

For a finite reduced root datum, the full ordered product is an open
immersion into the schematic closure of a supplied generic Chevalley
group over a Dedekind domain. Its pullback to every field-valued point is
therefore a nonempty smooth open chart. The general
`HasNonemptySmoothOpenChart.smooth` theorem makes each residue-field
fibre smooth. The closure is already flat and locally of finite
presentation, so `Smooth.of_smooth_fiberToSpecResidueField` gives
`genericModel_isSmooth`. The specialization `integerModel_isSmooth`
applies to the one fixed model over the lifted integers.

These are derived results using the integral open-cell identification,
the published polynomial and split-torus smoothness interfaces, and the
general chart and fibre smoothness criteria. They add no hypothesis about
connectedness of the whole closure's fibres.
