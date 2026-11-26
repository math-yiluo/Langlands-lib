# Compact-finite extraction from entire smooth real ordinary families

An entire bilinear spectral family on two smooth real standard modules can
supply covering ordinary tests if its evaluations are separately continuous
on a nonempty open spectral set, its smooth pure pairs give pointwise
coverage, and its restrictions to compact-finite pure pairs agree with
ordinary normalizations. The equal-rank assertion allows a Schwartz row,
held fixed during the passage to compact-finite vectors.

For each fixed vector in either argument, the entire linear evaluation
propagates continuity from the given open set to every spectral point. The
compact-finite vectors are dense in each smooth standard module. At a fixed
spectral point, vanishing on all compact-finite pairs would then give
vanishing on all smooth pairs by continuity in the first argument followed
by continuity in the second argument. A compact-finite pair with nonzero
evaluation gives actual ordinary Whittaker vectors through the supplied
intertwiners. The normalization agreement gives the desired nonzero value.

In H. Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), Theorem 2.3
(author-posted pp. 8–9) states the continuity of the original smooth
integral maps proved in §12.2 (pp. 87–89). The proof of Theorem 2.7 in §15
(pp. 108–109) uses that continuity and compact-finite density to extend
vanishing of a normalized evaluation to the smooth data. The Lean
argument implements this density step through separate continuity. It
assumes the entire family, continuity on the initial open set, pointwise
smooth coverage, and ordinary normalization agreement.
