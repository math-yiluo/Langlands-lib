# Segment induction from a minimal consecutive-run word

Author: Worker 320.

`MinimalIntegralCuspidalRunsSegmentInduction` concerns actual smooth complex
representations over an arbitrary supplied p-adic field and topology. The field
and carrier universes are independent; representation carriers are saturated
to `Type (max uF uV)`.

Fix an actual supercuspidal representation `A` of positive rank `m` and an
irreducible admissible finite-length representation `π` of positive rank `n`.
Supply finitely many runs with integer top labels `a i` and positive lengths
`l i`. Their concatenation is an actual integral cuspidal Jacquet word of `π`
on the twist line of `A`. Assume that no realized permutation of this word is
lexicographically smaller. Repeated labels and repeated runs are allowed; no
ordering of the top labels is required.

The explicit segment for run `i` has length `l i` and base class
`ν^(a i - (l i - 1)) A`, where `ν = |det|`. The conclusion first supplies the
equality between the sum of these segment degrees and `n`. It then supplies
actual irreducible admissible block representations `X i`, each satisfying
the strong `IsSegmentHead` relation for its explicit segment. That relation
retains equality of all irreducible quotient kernels. Their tensor is an
actual quotient of the whole normalized upper Jacquet module for the segment
block shape, and `π` actually embeds in their normalized product induction
in the supplied run order.

This is an internal derived statement. The actual word fixes the total degree.
Choose the fine shape by flattening the uniform cuspidal shapes within the
run blocks. Realization of the word identifies the actual tensor of twists of
`A` in that fine Jacquet module. Cuspidal first adjointness and induction in
stages give an embedding in the outer product of the run inductions. Lifting
through a whole Jacquet quotient supplies irreducible admissible coarse
factors occurring in those inner inductions. Each coarse factor realizes some
permutation of its run word. Actual Jacquet refinement reassembles those words
in `π`. A decreasing run is lexicographically greatest among its permutations,
so minimality forces each original run to be realized unchanged. The strong
decreasing socle of an individual segment then identifies each coarse factor
with the strong special head.

This file defines the proposition and supplies no proof. It assumes the
consecutive-run decomposition and its minimality; it does not construct an
initial twist line or that decomposition, reorder segment factors, or prove
analytic square-integrability or its classification.
