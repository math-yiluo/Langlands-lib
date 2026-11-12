# Almost-simple groups over separably closed fields are absolutely almost-simple

Author: Worker 96.

`Langlands.GroupScheme.separablyClosedAlmostSimpleAbsolute.{u}` proves exactly
the published `SeparablyClosedAlmostSimpleAbsoluteStatement.{u}`. For every
separably closed field `k : Type u`, an almost-simple group scheme over
`Spec k` remains almost-simple after the actual base change to
`AlgebraicClosure k`. The conclusion also retains its ground-field
almost-simplicity, as required by `IsAbsolutelyAlmostSimple`.

The theorem has no characteristic or perfectness restriction. Smoothness,
affineness and connectedness come from the semisimple part of the given
`IsAlmostSimple` predicate. The corrected condition on smooth connected
closed normal subgroups is used unchanged, on all test schemes.

## Source and provenance

The source theorem is J. S. Milne, *Algebraic Groups* (2017), Corollary 24.2
and preceding Proposition 24.1, printed p.512 / PDF p.528, registered as
`milne-2017-algebraic-groups`. The official errata, registered as
`milne-2017-algebraic-groups-errata-2026-11-02`, correct Definition 19.7 on
printed p.399. The Notes there identify geometric with absolute
almost-simplicity. The errata contain no correction to Corollary 24.2.

Milne's argument uses splitness and indecomposability of the root system.
The implemented proof instead combines the published actual-root and
normal-closure constructions. The three private lemmas are derived
internally from those interfaces; they introduce no structural premise or
new axiom. All their inputs are proved Library theorems.

## Implemented proof

First, `normalClosure_baseChange_le` treats a homomorphism `j : U ⟶ G`
and a supplied smooth connected normal closure `D`. After any extension
`K/k`, a closed normal subgroup containing the extended image of `j`
contains the extended image of `D.inclusion`. The proof uses
`EnvelopeBaseChange.range_baseChange_le_of_points` and the dominant finite
product map stored in `D.hasSmoothConnectedGeneration`. On every
`K`-scheme test, the pullback point equivalence identifies the conjugation
image with `x * j(y) * x⁻¹`. Normality gives its containment. The published
generated-image lemma then extends containment from these points to the
whole extended normal closure.

Next, `exists_full_root_normalClosure` works over any ground field with a
specified split maximal torus and an almost-simple ambient group.
`RelativeRoot.rootSubgroupRealization` supplies a smooth connected closed
representative of each actual root functor and its exact positive Lie
image. This root functor is nontrivial: its positive weight span is
nonzero, whereas the identity functor has zero tangent submodule.
The smooth connected normal closure is consequently nontrivial.
Ground-field almost-simplicity forces its range to be the whole group.

The third lemma, `almostSimple_baseChange_of_split_maximalTorus`, extends
such an almost-simple group to any algebraically closed extension field.
Semisimplicity and maximality of the split torus persist by
`isSemisimpleFieldExtension` and `maximalTorusBaseChange`.
Noncommutativity follows from nontriviality of the semisimple extended
group: fpqc reflection of the identity subgroup would otherwise make
every ground-field point the identity and contradict the original
noncommutativity.

For a smooth connected closed normal subgroup of the extended group,
suppose its range is proper. Apply
`semisimpleNormalRootDichotomy_of_rootLines`, supplying the proved
`normalReductiveCenter`, `semisimpleRootGeneration`,
`absoluteRootVectorLine` and `maximalTorusConjugacy`. Each root functor
either lies in the subgroup or centralizes it. The first alternative is
impossible. The split-torus character base-change equivalence and
`mem_roots_baseChange_iff` identify that root with an original root.
`RelativeRoot.subgroup_baseChange` identifies its functor with the
extended original representative. The first two private lemmas then put
the whole extended group in the supposedly proper subgroup.

Thus every root centralizes the subgroup. The published
`AutomorphicAction.fixedSubgroup_eq_top_of_rootGeneration` makes its full
centralizer equal to the whole ambient group. Monicity of the closed
inclusion implies that the subgroup itself is commutative on every test.
It is also semisimple, by the normal-subgroup theorem with
`normalReductiveCenter`. A nontrivial semisimple group over an
algebraically closed field is noncommutative, by
`IsSemisimple.noncommutative_of_range_ne_bot`. The subgroup therefore has
identity range. This proves the required normal-subgroup dichotomy.

Finally, separable closedness supplies a split maximal torus by
`exists_isMaximalTorus_isSplitTorus_of_isSepClosed`. Apply the third lemma
with `K = AlgebraicClosure k` and pair the result with the given
ground-field almost-simplicity. No descent of an arbitrary inseparable
normal subgroup is needed. The theorem and its imports do not use the
Weil-restriction host theorem or a Local Kneser–Tits consumer.
