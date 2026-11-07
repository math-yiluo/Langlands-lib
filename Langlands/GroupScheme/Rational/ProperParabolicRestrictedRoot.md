# A restricted root witnessing a proper actual parabolic

This is derived internal support for the unitary-exponent argument in Renard
VII.2.4. It retains the supplied actual parabolic map `p`, rational Levi `l`,
split component `a`, and compatible `ParabolicRootPresentation r`. The field
has arbitrary universe, the ambient group is connected reductive, and ambient
affineness and local finite type are explicit. No representation-theoretic or
parabolic-correspondence statement is assumed.

If the complementary restricted roots are empty, the presentation's selected
simple roots are the full simple-root set. The proved full-index endpoint
identifies the supplied parabolic's range with the whole ambient group.
Its closed representative is consequently an isomorphism. Conversely, when
the supplied parabolic is full, its original rational Levi is an isomorphism
by reductivity; the established full-Levi root lemma gives the empty
restricted-root set.

Thus every proper actual parabolic has a nonempty restricted-root set in
every compatible presentation. `properRestrictedRoot` selects a member of
this actual set. Its defining split-component evaluation is strictly
positive by the established evaluation lemma. The same evaluation criterion
excludes zero from the strict positive cone of every proper presentation.
The construction also handles ambient split rank zero: in that case its
properness premise cannot hold for a supplied compatible presentation.

The accompanying representation adapter uses this exclusion to prove that
strictly positive normalized exponents force the unitary Jacquet part to
vanish along a proper actual parabolic. These conclusions do not establish
Casselman's analytic criterion or the converse face argument for VII.2.4.
