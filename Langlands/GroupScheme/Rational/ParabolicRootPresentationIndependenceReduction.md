# Full presentation independence from actual root reflections

`ParabolicRootPresentationReflectionReductionStatement` is the explicit
conditional proposition

```
RelativeRootReflectionExistenceStatement →
  ParabolicRootPresentationIndependenceStatement ∧
    ParabolicRootPresentationIsoStatement.
```

It is proved in this module at arbitrary universe `u`. The reflection-existence
premise is retained; the module does not prove it or the exact unconditional
aggregate `ParabolicRootPresentationStatement`.

## Comparison of arbitrary presentations

For any field and affine smooth group scheme, fix the actual maps
`p : P → G`, `l : M → P`, `a : A → M`. The theorem
`restrictedRoots_eq_of_simpleRoot_hypotheses` compares any two compatible
presentations `r` and `s`, allowing all their torus, embedding, generic
cocharacter, root-index and factor choices to differ. It assumes rational
independence of each ambient simple-root family and negation stability for
each ambient actual root set.

The proof identifies each restricted-root set with the real image of its
intrinsic simple positive component weights, using
`restrictedRoots_eq_image_intrinsicSimpleRoots`. The existing intrinsic-support
independence theorem makes these two intrinsic simple sets equal. This proves
the restricted-root equality in the full real character space of the specified
component `A`.

## From actual reflections to the exact targets

`parabolicRootPresentationIndependenceStatement_of_reflections` assumes the
existing universal `RelativeRootReflectionExistenceStatement`. For every
connected reductive group and any two compatible presentations it obtains
actual reflection data separately for their two maximal split tori. The
published reflection API supplies rational simple-root independence (using
actual root finiteness and the given generic cocharacter), and root negation.
Applying the preceding comparison gives restricted-root equality. The published
finite root-combination congruence theorem then gives both the positive and
nonnegative cone equalities required by the exact universal independence target.

`parabolicRootPresentationIsoStatement_of_reflections` combines that exact
independence statement with compatible component pullback. It yields all six
forward and inverse character-pullback equalities for restricted roots and both
cones, even when all presentation choices vary. No presentation-existence or
additional conjugacy hypothesis is used for this implication.

`parabolicRootPresentationReflectionReduction` proves the named conditional
proposition. Finally,
`parabolicRootPresentationStatement_of_existence_of_reflections` also assumes
the exact universal `ParabolicRootPresentationExistenceStatement`; it assembles
the exact aggregate using the independence and component-isomorphism results.
Both structural inputs remain explicit.

## Provenance and remaining scope

This is internal derived content, combining the actual reflection independence
and negation APIs with the intrinsic simple-root comparison, intrinsic support
independence, finite cone congruence and compatible component pullback. It makes
no new source assertion. The included helper pairs are unchanged supporting
units submitted separately for independent review and integration.

All fields, actual specified maps, unrestricted presentation choices, nonreduced
root sets, empty-root cases, full real character spaces and both cones are
retained. General actual reflection existence and general specified-map
presentation existence remain separate unproved obligations. This supporting
statement and its conditional proofs do not discharge the host task.
