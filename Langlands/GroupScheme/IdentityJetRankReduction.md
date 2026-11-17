# Variable-rank reduction of actual Lie determinant-dual positivity

This internal unit removes the global fixed-index cover hypothesis from
the actual jet-to-Lie positivity reduction, retaining explicit jet
positivity or base-change inputs.

Let `G` be a smooth affine group scheme over a compact quasi-separated
scheme `S`. The definition `cotangentRankFrames` chooses actual finite
local cotangent frames. Its clopen `rankOpen k` loci form the previously
proved disjoint cover of `S`. `rankBaseGroup G k` is the actual group
scheme obtained by base change along the inclusion of the rank-`k`
locus. It is again smooth and affine.

The theorem `rankBaseGroup_exists_affineCover` supplies actual
cotangent frames of this group over an affine cover with the fixed
index `ULift (Fin k)`. The rank-locus construction first gives frames
of the actual pulled-back original cotangent sheaf. The canonical
cotangent base-change isomorphism, which is invertible without a
smoothness restriction, transports them to the actual cotangent
sheaf of `rankBaseGroup`.

The theorem `lieDeterminantDual_isAmple_of_rankJets` assumes that for
every rank locus some positive-order actual jet determinant of its
actual base-changed group is ample. The jet order may depend on the
rank. On that locus the fixed-index jet-to-Lie comparison proves
ampleness of its actual Lie determinant dual. The canonical smooth
Lie determinant base-change isomorphism and actual dual-pullback
comparison identify this bundle with the inclusion pullback of the
original actual Lie determinant dual. Ampleness on the disjoint rank
cover then assembles on `S`.

The theorem `lieDeterminantDual_isAmple_of_jet_rankBaseChange` gives a
second, more specific reduction. Assume a positive-order original
actual jet determinant is ample and, for each rank locus, supply an
actual module-sheaf isomorphism from the pullback of the original
jet module to the actual jet module of `rankBaseGroup` at that same
order. Each rank inclusion is closed as well as open, hence affine;
original jet ampleness pulls back. The actual finite locally free
determinant pullback and module-isomorphism comparisons transport
this ampleness to the rank group's actual jet determinant. The first
reduction then applies.

The provenance is internal: this combines actual clopen rank frames,
canonical cotangent and Lie determinant base change, the fixed-index
jet-to-Lie comparison, actual determinant functoriality and disjoint
open-cover ampleness assembly. No global constant-rank, noetherian or
nonempty-index assumption is added. The second reduction explicitly
requires the actual jet-module base-change isomorphisms; this unit
does not construct them or establish jet positivity. Those inputs
and the final finite-parabolic specialization remain obligations.
