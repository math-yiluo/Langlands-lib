# Actual Levi multiplicities and the Weyl equality-test bridge

This target unit fills the explicit realization gap between the source's
actual Levi-intersection count and the intrinsic Weyl-subgroup count in
`RelativeWeylIndexingTargets`. The construction uses the actual quotient
`W = N_G(T)/Z_G(T)` and the proved quotient action in
`RelativeWeylConjugation`. It makes no representation-theoretic assertion.

## Source and scope

Aubert, *Dualité dans le groupe de Grothendieck des représentations lisses
de longueur finie*, 1995, printed p.2182 / PDF p.4, after equation (1.8),
defines `a_{J,I,K}` for `K ⊆ J` as the number of `w ∈ D(I,J)` for which
`L_J ∩ w⁻¹ L_I w = L_K`. She then uses the signed sum
`sum_I (-1)^|I| a_{J,I,K} = (-1)^|K|`, citing Solomon through Carter
Proposition 2.7.7. The registered source is `aubert-1995-duality`, SHA256
`57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`.
The original page was read directly. This is not an independent reading or
proof of Carter's proposition.

Renard V.4.3, printed p.119 / PDF p.125, gives the full-centralizer Weyl
quotient, Levi embedding and lift-independent conjugation of Levis containing
the minimal centralizer. The registered 9 July 2026 source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Those elementary subgroup constructions are already implemented in the
imported pairs; the present unit uses that action without a chosen lift.

The inputs are a group `G`, an actual subgroup `T`, a family `L` of actual
subgroups containing `Z_G(T)`, and an actual Coxeter system on the quotient.
`L` is a parameter of realization targets. There is no claim that an arbitrary
such family is a family of standard Levis or satisfies the targets.
The shared standard-parabolic adapter must specialize `T` to the maximal
split torus and `L I` to the actual standard Levi with
`L empty = Z_G(T)`. It must also identify the simple generators, the finite
quotient and its minima with the rational-point relative-root construction.
These comparisons remain obligations, including the nonsplit,
non-quasisplit and positive-characteristic cases allowed by that adapter.

## Declarations

`actualRightIntersection T L I J w` constructs the subgroup
`L_J ∩ w⁻¹ L_I w`. It takes the inverse Weyl element in the quotient action,
so `actualRightIntersection_mk` gives precisely
`L_J ∩ n⁻¹ L_I n` for every normalizer lift `n`. Lift independence is inherited
from the imported construction, rather than postulated here.

`actualIntersectionMultiplicity` filters the actual finite set of minimum
representatives `D(I,J)` by equality of that actual intersection with `L_K`
and takes its cardinality. This is the actual-subgroup counterpart of the
source's count. Identifying its indexing set with the source still needs the
root/minimality comparison.

`actualIntersectionEqualityCriterion` is the new pointwise target. For each
minimum representative and `K ⊆ J`, it states the equivalence

`L_J ∩ w⁻¹ L_I w = L_K  iff  W_J ∩ w⁻¹ W_I w = W_K`.

The Weyl subgroups on the right are the actual generated Coxeter subgroups.
Neither the quotient injection nor lift independence alone proves this
criterion. Its proof needs the actual standard-Levi and root realization,
including the faithfulness of the standard-Levi subset classification and the
corresponding standard-Weyl subgroup classification. This retains the
realization work under D06 in the published Chapter V ledger, using S14–S15
where appropriate. It does not add an external structural assertion.

`actualMultiplicityComparison` states equality of the actual and intrinsic
counts for all `I,J,K` with `K ⊆ J`. The helper
`actualMultiplicityComparison_of_equalityCriterion` proves this conditional
comparison by extensionality of the filtered finite sets and the pointwise
criterion. It proves no instance of that criterion.

`actualSolomonCancellation` states the alternating sum with actual Levi
multiplicities, using the same integer signs and all simple-index subsets as
the source. Its intended proof combines the count comparison and the
separately named intrinsic `solomonCancellation`; neither is assumed as a
field of construction data. No proof of this cancellation or of an Aubert
identity is supplied. The empty-index case is included: there is no positive
rank or nonempty-root hypothesis.

## Dependency boundary

The finite cancellation is a separate proof obligation; it is not part of the
external Chapter V structural boundary or an imported classification result.
Continuity, smooth representation conjugation, geometric-lemma K0 expansion,
Weyl-conjugacy of induced classes and all Theorem 1.7 assertions remain with
the existing functor and proof owners. The use of actual subgroups in this
unit provides no proof of any of those representation-theoretic inputs.

Worker 164's private source coordination identified the need for the pointwise
equality-test bridge and explained the separate Chapter V source boundaries.
Worker 165 authored this Lean/Markdown pair; both contributions are attributed
in the submission.
