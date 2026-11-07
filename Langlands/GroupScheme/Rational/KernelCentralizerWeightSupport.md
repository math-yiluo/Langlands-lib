# Integral character support and full character-kernel centralizers

Author: Worker 1465.

This internal support unit uses the published integral-weight description of the
full scheme-theoretic character-kernel centralizer. All statements are uniform
in the universe and allow positive characteristic and nonreduced kernels.

`mem_zmultiples_of_weightSpace_integralWeightSpan` says that a nonzero vector
which is both a character-weight vector and in the integral weight span has
character in the actual subgroup of integer multiples. The proof projects to
that weight in the split-torus direct sum. If the character were outside the
integer multiples, the projection would vanish on each summand of the span and
hence on the vector, contradicting its nonzero value.

`root_restrict_mem_zmultiples_of_range_le_kernelCentralizer` applies this to a
monic subgroup whose full range is contained in a character-kernel centralizer.
A nonzero vector in any of the subgroup's torus-root spaces maps injectively to
the ambient Lie algebra. Its character restricts along the specified torus map,
and its actual dual-number point belongs to the centralizer. The published
kernel tangent and integral support results then give the required integer
multiple. No maximality or reductivity of either group is assumed here.

`integralWeightSpan_eq_top_of_root_restrictions` runs the other direction for
all weights: if every nonzero root restricts to an integer multiple, every
summand of the split-torus weight decomposition lies in the restricted integral
span. Zero weights restrict to zero. The span is therefore the whole Lie
algebra.

`kernelCentralizer_eq_top_of_integralWeightSpan_eq_top` concerns a smooth
connected affine group and a nonzero character of a split torus mapping to it.
The published kernel-centralizer structure theorem provides a smooth closed
representative and the exact integral tangent image. The full-span hypothesis
makes its tangent map surjective. The published smooth closed-subgroup Lie
equality theorem makes the inclusion an isomorphism. Inverting that morphism
shows the range is the whole group on every scheme test.

`kernelCentralizerIsoOfIntegralWeightSpanEqTop` constructs the canonical
isomorphism from any representative of that centralizer to the ambient group.
It first uses the preceding all-test equality to view the inclusion as a
representative of the full subgroup, then compares it with the identity
representative. Its forward morphism is proved equal to the original
inclusion by `kernelCentralizerIsoOfIntegralWeightSpanEqTop_hom`.

The provenance is internal composition of split-torus weight decomposition,
actual Lie-kernel functoriality, the published full-kernel structure proof, and
the smooth connected closed-subgroup equality theorem. The hypotheses on root
restrictions and tangent support remain explicit. This unit does not yet prove
the host's unconditional component reductivity statement.
