# Parabolic subgroups of reductive group schemes are self-normalizing: proof

Author: Worker 33. The route is the one recorded by Worker 3483 (Task 3483) in the context
of this proof task; Worker 3483's draft files were not available here and were not reused,
and the Lean file was written anew.

`Langlands.GroupScheme.relativeParabolicSelfNormalizer` proves exactly the published
proposition `Langlands.GroupScheme.RelativeParabolicSelfNormalizerStatement.{u}` of
`Langlands.GroupScheme.RelativeParabolicNormalizerStatement`
([`RelativeParabolicNormalizerStatement`](RelativeParabolicNormalizerStatement.md)), at an
arbitrary universe `u` and with no added premise.

For every commutative ring `R : Type u`, all group schemes `G P` over
`Spec (CommRingCat.of R)` and every homomorphism `i : P ⟶ G` such that `G` is reductive,
`P` is smooth over `Spec R`, `i` is a closed immersion, and the base change of `i` to every
field `k : Type u` with `[Algebra R k]` is parabolic, the theorem gives

```lean
(SubgroupFunctor.range i).normalizer = SubgroupFunctor.range i
```

as subgroup functors on all tests `U : Over (Spec (CommRingCat.of R))`, including
non-affine and nonreduced tests. This is the first assertion of Conrad, *Reductive group
schemes* (2014), Corollary 5.2.8, for an affine base, as explained in the statement's
Markdown.

## Implemented proof

The proof is one term. After introducing `R`, its ring structure, `G`, `P`, `i` and the
four hypotheses `hG`, `hPsmooth`, `hi`, `hP`, it applies the published conditional theorem

- `Langlands.GroupScheme.RelativeParabolicNormalizerReduction.normalizer_eq_of_statements`,
  module `Langlands.GroupScheme.RelativeParabolicNormalizerReduction`
  ([`RelativeParabolicNormalizerReduction`](RelativeParabolicNormalizerReduction.md)),

whose three proposition premises are supplied by the published proofs

- `Langlands.GroupScheme.relativeSelfNormalizer : RelativeSelfNormalizerStatement.{u}`,
  module `Langlands.GroupScheme.RelativeSelfNormalizerProof`
  ([`RelativeSelfNormalizerProof`](RelativeSelfNormalizerProof.md)): a smooth closed
  subgroup with geometrically connected fibres of a smooth affine group scheme over any
  scheme is self-normalizing on all tests once this holds after every field-valued base
  change;
- `Langlands.GroupScheme.parabolicSelfNormalizer : ParabolicSelfNormalizerStatement.{u}`,
  module `Langlands.GroupScheme.Rational.ParabolicNormalizerProof`
  ([`Rational.ParabolicNormalizerProof`](Rational/ParabolicNormalizerProof.md)): over a
  field, a parabolic subgroup of a connected reductive group is its own normalizer on all
  tests;
- `Langlands.GroupScheme.parabolicDynamic : ParabolicDynamicStatement.{u}`,
  module `Langlands.GroupScheme.Absolute.ParabolicDynamicProof`
  ([`Absolute.ParabolicDynamicProof`](Absolute/ParabolicDynamicProof.md)): over a field, a
  closed subgroup of a connected reductive group is parabolic exactly when its range is the
  dynamic parabolic of a cocharacter.

Its remaining four arguments are exactly the four hypotheses of the target, passed in the
same order. Inside the published reduction, `parabolicDynamic` and the published
`dynamicConnected` give geometric connectedness of `P`; `parabolicSelfNormalizer` gives
self-normalization after every field-valued base change, using that base changes of `G`
to fields are connected reductive and base changes of `i` are parabolic; and
`relativeSelfNormalizer` turns these field-fibre equalities into the all-test equality over
`Spec R`.

No other published theorem is invoked directly by this file. The module imports the
statement module, the reduction module and the three proof modules above, and adds only
this theorem: no definitions, other theorems or axioms. A development check reports only
the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
