# The normalized orbital profiles of regular division units

`regularDivisionOrbitalProfile.{u}` proves `RegularDivisionOrbitalProfileStatement.{u}`.
For a regular division unit `a`, take a compact open coefficient window in the
domain of the regular coefficient section. All values of the section have the
centralizer of `a`. The map from the product of the window with the left quotient
by this centralizer sends a coefficient vector and a coset to the corresponding
conjugate of the section value. It is continuous by the open quotient map.
Equal coefficients determine a conjugacy class, and equal conjugates in a
single fibre differ by the centralizer. These facts give bijectivity onto the
inverse image of the coefficient window. The quotient is compact because the
centralizer contains the center. The window is compact and the target is
Hausdorff, so the map is a homeomorphism.

The division unit group is unimodular, and the regular centralizers are
commutative with largest compact open subgroups. These facts give normalized
centralizer measures and compatible quotient measures by
`RegularOrbitalMeasures.exists_isNormalized`.
`regularOrbitalProfilesFromCharts` uses the product charts to integrate regular
Schwartz–Bruhat tests, to prove local constancy in the coefficient coordinate,
and to descend the integral on each parameter fibre.

The result supplies the regular orbital profiles used for Badulescu's local
transfer (2002), §5, printed p. 733, and §6, printed pp. 745–746. Source
`badulescu-2002-jl-char-p`, registered folder SHA-256
`dc96cc7848166e83a1f23478a1e341928ea8565bc9b649ffe84e452f3a205028`, published PDF
SHA-256 `638e7134bb13c9c718ee7e5c2c9f06634637598c6ba8cd465345baf1234ed370`.
