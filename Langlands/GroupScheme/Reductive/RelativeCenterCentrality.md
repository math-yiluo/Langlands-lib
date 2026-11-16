# Diagonalizable centrality from the adjoint action

This internal derived criterion supplies the centrality step of the construction
of relative centres. It uses the existing actual smooth closed centralizer of a
diagonalizable group over an arbitrary commutative ring, including character
groups with torsion. The homomorphism need not be a closed immersion.

First, triviality of the adjoint action over every coefficient algebra implies
that the conjugation action after any affine base change has its entire Lie
module as invariants. The proof uses the published actual base-change linear
equivalence of dual-number Lie kernels and its compatibility with the adjoint
action and with homomorphisms of group schemes.

For a reductive ambient group over an arbitrary ring, the actual centralizer is
smooth. On each residue fibre it is a smooth closed subgroup with the full Lie
image. The published field Lie-subgroup equality theorem identifies that fibre
with the connected smooth ambient fibre. The published fibrewise isomorphism
criterion then makes the original centralizer inclusion an isomorphism. Thus
its all-test centralizer is the entire group, which gives centrality on every
test scheme and every refinement. The construction
`relativeCentralizerIsoOfAdjointEq` records this isomorphism; its forward
homomorphism is exactly the existing actual centralizer inclusion.

These statements do not construct the centre or prove its multiplicative type.
They implement the centralizer comparison used in the relative-centre argument
of Conrad, *Reductive group schemes* (2014), Theorem 3.3.4, pages 98–99. Their
provenance is the existing smooth diagonalizable centralizer construction,
field Lie-subgroup equality, residue-fibre reductivity, and the smooth
fibrewise isomorphism criterion; no additional structural theorem is assumed.
