# Similitudes of the actual rational frame

`orderAut` is the subgroup of actual tower automorphisms in the rational
category that commute with every order endomorphism. The usual
composition and inverse of rational order-linear maps give its group
operations. `SplitFrameSimilitudes` combines an element of this group
for the primal tower with one unit of `ℚ_p`. `splitFrameAut` sends it
to the order-linear map with primal block `g` and dual block
`c * (g⁻¹)∨`. Composition of split rigidifiers proves that this is a
group homomorphism.

`PolarizedFramedTower.frameAction` acts on the classes of actual
polarized framed tower data by precomposing the rigidifier with the
inverse of the frame automorphism. The target isomorphism still
intertwines the rigidifiers because rational composition is
associative. The same identity gives the left action law.

Harris (1997), Appendix, printed p. 113 (PDF p. 39), uses this inverse
precomposition in the action of the frame similitudes on C1. In
Rapoport–Zink (1996), Definition 3.22, printed p. 82 (PDF p. 96), it is
the left action on framed pairs. The split description here uses the
actual rational tower of the primal frame. Rapoport–Zink (1996), §6.43,
printed p. 309 (PDF p. 321), gives the corresponding split form of the
polarized frame.
