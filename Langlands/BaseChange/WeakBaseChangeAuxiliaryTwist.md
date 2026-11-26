# A common auxiliary Hecke twist for weak base change

`WeakBaseChangeAuxiliaryTwistStatement` takes a cyclic Galois extension
of number fields with compact adelic quotients, a distinguished lower
finite place, and two pairs of cuspidal spectral presentations of the
same rank. All four presentations have irreducible admissible finite
components. The upper forward presentation is an arithmetic weak base
change of the lower forward presentation. The second presentation over
each field supplies the standard factors for the inverse twist. Its
identification with the global contragredient is used separately.

There exists a finite-order lower Hecke character trivial at the
distinguished place, with idelic norm pullback trivial at every place
above it. At every other lower finite place, either the original forward
spectral systems have defined spherical parameters related by the
residue-degree power, or their common twists satisfy the highly ramified
standard factor formulas. The lower formulas apply after multiplying the
common local twist by any character trivial on norms from an upper
completion. The upper formula uses the local component of the idelic norm
pullback. The inverse characters give the formulas for the second pair of
presentations. All these formulas apply to every certified standard
factor choice with its trivial rank-one partner and standard finite
additive component.

The complement of the places with spherical power data is finite.
Remove the distinguished place and choose, at every remaining bad place,
the maximum of the conductor bounds for the forward and second
presentations. The global norm-character restriction theorem exhausts
the local norm characters, and `globalHeckeNormTwistDepth` gives a
single character meeting the lower and upper bounds. The conductor
of a quasicharacter is unchanged by inversion, so these same bounds
apply to the inverse twists.
