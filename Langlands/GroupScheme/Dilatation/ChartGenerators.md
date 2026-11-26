# Regular equations for a centre in local coordinates

`exists_regular_generators` produces a regular list of generators of an ideal \(I\) in a regular local ring \(A\) when \(A/I\) is regular local. It chooses a generating list of length equal to the minimal number of generators of \(I\). For the surjection \(A\to A/I\), this length plus the dimension of \(A/I\) equals the dimension of \(A\). A regular local ring is Cohen–Macaulay, so the dimension criterion makes the chosen list regular.

`exists_lifted_regular_generators` applies that result to the image of \(I\) in \(A/(t)\) when \(t\in I\) and both \(A/(t)\) and \(A/I\) are regular local. Lifting the list back to \(A\) gives elements that, together with \(t\), generate \(I\). Their reductions modulo \(t\) form a weakly regular sequence.

The regular-local-ring argument implements the regular equations used for the
smooth centre in Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*, Appendix
A.5.10, printed p. 635. The proof uses the Library's dimension criterion
`Module.IsMaximalCohenMacaulay.isRegular_iff_ringKrullDim_add_length_eq_ringKrullDim`.
[DimensionCriterion](../../../StacksFrontier/RingTheory/CohenMacaulay/RegularSequence/DimensionCriterion.md)
