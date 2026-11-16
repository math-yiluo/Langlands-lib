# Rigidity of the numbered type-G2 Cartan matrix

This internal module uses Mathlib's actual matrix
`CartanMatrix.G₂ = [[2,-3],[-1,2]]`.
`IsTypeG2Numbering M e` means that the supplied equivalence identifies
every ordered integral entry of `M` with this matrix.

`CartanG2Numbering.eq_neg_three_iff` checks the four entries by ordinary
kernel-checked finite cases: the entry is minus three exactly at the
ordered pair `(0,1)`. Therefore a map preserving every entry fixes both
vertices, as `CartanG2Numbering.rigid` proves.
`CartanG2Numbering.unique` applies rigidity to one numbering composed
with the inverse of another and concludes equality of the numberings.

This is elementary integral matrix combinatorics and introduces no new
literature translation. It asserts neither the existence of actual
group schemes of a given type nor any classification theorem.
