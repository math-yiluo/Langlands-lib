# Correcting local morphism pullbacks by function primitives

`ClosedFormBasis` is a family of compatible closed one-forms on the target
whose restrictions are coordinate-ring bases of the relative differentials
on the tuple intersections. `LocalPullbacks.correctedSections` takes, for
each such form, a function zero-cochain on the source with values in the
extended base ideal. For any intersection and local pullback at a vertex,
it defines a contraction on target one-forms by specifying its value at
each basis vector to be the restriction of the corresponding function from
that vertex. The correction subtracts the contraction of the differential
of each function from its original pullback.

The contraction takes values in the extended ideal. Products of any two
such values vanish by the square-zero assumption, so the Leibniz identity
for the differential proves that the corrected maps are algebra maps.
They reduce to the original maps, and the expansion in the common bases
shows that they commute with restriction at a fixed vertex.

`correctedSections_eq_of_primitives` assumes that the Čech coboundaries
of the cochains are the respective difference contractions. On a pair
intersection, the difference of the two vertex corrections then agrees
with the difference contraction on the basis. The two actions on the
ideal coefficients agree because the local pullbacks are congruent
modulo that square-zero ideal. Therefore the equality extends to all
one-forms. Applying it to exact forms gives equality of the corrected
algebra maps on the overlap.

These identities give the affine algebra step in the converse of
Proposition 2.1.6.9 of Kai-Wen Lan, *Arithmetic compactifications of PEL-type
Shimura varieties*, revised 14 March 2021, printed p. 136 (PDF p. 164).
The retained source is `lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
