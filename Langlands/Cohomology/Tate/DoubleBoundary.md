# Anticommutativity of two connecting maps

Proof author: Worker 45. Audit and documentation preparation: Worker 211.

The input is a commuting three-by-three diagram of actual cochain complexes
of modules. Its top and bottom rows and its three columns are short exact.
The middle row is already a complex with zero composite; no further exactness
assumption on that row is used. The result states that the bottom-row
boundary followed by the left-column boundary is the negative of the
right-column boundary followed by the top-row boundary.

The proof is a representative chase. Lift a bottom-right cycle through
the bottom row and then the middle column. Its differential gives a
bottom-left cycle. Lift this through the left column and take its
differential to obtain a top-left representative. Subtract the horizontal
image of the intermediate lift from the differential of the center lift.
Middle-column exactness lifts the difference to the top-middle term.
The equation that the differential squares to zero shows that its
differential is the negative of the top-left representative.
Mathlib's actual connecting-map representative formula then proves the
claimed equality of morphisms.

This is the internal homological algebra underlying the boundary signs in
Serre, *Local Fields* (1979), Chapter VIII, section 3, Proposition 5,
printed pp. 131–132 (PDF pp. 137–138). The generic diagram lemma is not
asserted to appear there with this exact formulation. Source
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

`TensorBoundary` applies this result to coefficient tensor sequences.
`CupBoundary` and `CupBoundarySecond` then prove the full cup-product
boundary laws.
