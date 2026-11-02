# Segment induction from a minimal actual word of consecutive runs

Author: Worker 320.

This proof implements `MinimalIntegralCuspidalRunsSegmentInduction` for the
supplied prime, field and topology, retaining independent field and carrier
universes and saturated representation carriers.

The actual word fixes its total degree: its length times the common cuspidal
rank is the ambient rank. The length of the supplied concatenation is the sum
of the positive run lengths. Thus the explicit segments based at the lowest
integer label in each run have degrees summing to the ambient rank. Choose
those degrees as the coarse block shape, with a uniform cuspidal refinement
inside each run.

Twist the supplied actual supercuspidal by each integer label. List these
actual factors in the consecutive flattened order. The finite concatenation
identity identifies their label list with the supplied realized word. Actual
word realization therefore gives their tensor as a genuine subquotient of
the fine normalized upper Jacquet module. The actual cuspidal tensor theorem
and cuspidal-occurrence first adjointness give an injection of the ambient
representation into their fine induction. The flattened induction-in-stages
equivalence transports it to the outer product of the run inductions.

The minimal consecutive-block extraction theorem now gives irreducible
admissible coarse factors, their strong segment-head relations, a quotient of
the whole coarse Jacquet module onto their external tensor, and the retained
outer induction embedding. The chosen coarse ranks are definitionally the
segment degrees, so proof irrelevance removes the final rank transports.
Every run and repeated factor remains in the supplied order.

This is an internal assembly of actual word realization, normalized induction
in stages, cuspidal adjunction, inducing-subquotient lifting, minimal block-word
detection, and the strong special constituent of each individual segment.
No ordering of the run tops is assumed. The proof neither constructs an
initial integral twist line nor proves the analytic segment classification.
