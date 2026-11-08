# Rank-one centralizers in smooth Borel overgroups

Worker 146. These internal lemmas are derived from the published split-root Lie-line theorem, reducedness of the actual root system, maximal-torus self-centralization and the dynamic centralizer tangent-containment helper.

The first lemma upgrades occurrence of a root in the actual tangent-weight support of any subgroup functor to containment of its full root line. The published root-space linear equivalence identifies its dimension with one; any nonzero vector in the intersection spans that line. No smoothness or stability of this subgroup is required.

The second lemma considers a smooth connected closed subgroup P containing the given split maximal torus of a connected reductive G. For a root whose two signs occur in the tangent support of P, the actual generic rank-one cocharacter centralizer is contained in P. Its Lie algebra is the sum of the weight spaces with zero pairing. Every nonzero such root is dependent with the chosen root by genericity, hence equal or opposite by root reducedness. The first lemma puts both of these root lines into Lie(P). Self-centralization of the maximal torus puts the zero weight in Lie(T), hence in Lie(P). The cocharacter factors into P through the displayed torus lift, so `Dynamic.centralizer_le_range_of_tangentSubmodule_le` turns this tangent containment into containment on every test scheme.

The conclusion depends on the displayed smoothness and connectedness of P. This is an intermediate result; it does not yet construct the final overgroup cocharacter or remove connectedness as a premise of the target statement.

`AbsoluteBorelOvergroupRankOneContainmentStatement` is the Prop-valued universal interface of the second lemma, with all of its hypotheses displayed. This candidate publishes that intermediate statement and the accompanying implementation helpers. It is not a proof record for the final `AbsoluteBorelOvergroupCocharacterStatement`; the final exact-target proof and its independent proof validation remain required.
