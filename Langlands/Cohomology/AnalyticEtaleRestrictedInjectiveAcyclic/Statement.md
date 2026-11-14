# Acyclicity of restricted injective étale G-sheaves

This module states an internal prerequisite for the analytic étale comparison
theorems. It contains no proof of acyclicity.

The parameters are a complete ultrametric normed field `K`, a normed extension
field `L`, an analytic space `X`, the point axioms `h` for its `L`-valued points,
a topological group `G` acting by analytic automorphisms through `ρ`, and a
commutative coefficient ring `R`. The universe levels, smallness of `G`, and
admissible-refinement instance are those of the compact comparison statement.
Each of the three proposition definitions explicitly binds `IsTopologicalGroup G`,
`Small.{max u (v + 1) uL} G`, and `HasAdmissibleRefinements`, so all three
hypotheses remain in its exported type.
Sheafification on the twisted étale site supplies the abelian category in which
injectivity is interpreted.

`AnalyticEtaleRestrictedInjectiveCompactAcyclicStatement` says that if `|X|` is
Hausdorff, every underlying point is the image of an `L`-valued point, and the
action is continuous, then for every injective object `I` of `EtaleGSheaf ρ`
the module
`H_c^(q+1)(X, b^* I)` is zero for every natural number `q`. Here `b^*` is exactly
`etaleGSheafRestriction`, and the cohomology is exactly
`etaleCompactCohomology L h R`, using the Library's supports in `L`-valued
points.

`AnalyticEtaleRestrictedInjectiveGlobalAcyclicStatement` asserts
`H^(q+1)(X, b^* I) = 0` under the same hypotheses and the additional assumption
that `|X|` is compact, using `etaleCohomology`. Its declaration does not depend
on `h`: ordinary cohomology does not use this point family. It retains
surjectivity of `pointProjection L X`.

`AnalyticEtaleRestrictedInjectiveAcyclicStatement` is the conjunction of these
two statements. Injectivity is required in the equivariant category before
restriction. The statements assert acyclicity after restriction, without
asserting preservation of injective objects by `b^*`.

The provenance is derived. Berkovich's 1995–1996 equivariant manuscript,
§1.5, Proposition 1.5.1, pp.10–11, proves softness of the restricted equivariant
Godement terms. Its Corollary 1.5.2, pp.11–12, uses that result for the
cohomological comparisons. Berkovich, *Vanishing cycles for formal schemes*
(1994), §3, Lemma 3.2(i), printed p.544, gives the ordinary acyclicity of soft
étale sheaves on paracompact spaces. Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), §5.1 and Theorem 5.2.2, printed
pp.97–99, supplies the supported-cohomology framework and the Leray argument
through the ordinary topology and local Galois cohomology.

The proposed independent proof route is to establish a monic equivariant
Godement coaugmentation and the softness and compact-support acyclicity
ingredients, then use injectivity to make `I` a retract of its degree-zero
Godement term. Acyclicity passes to the restricted retract. On compact `X`,
all global sections have compact support in the Library's point topology, so
ordinary and compactly supported cohomology agree. These are proof
obligations, not facts proved in this module; in particular, neither
comparison theorem may be used to justify this prerequisite.
