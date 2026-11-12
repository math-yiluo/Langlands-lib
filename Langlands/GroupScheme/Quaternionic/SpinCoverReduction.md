# Spin-cover existence, uniqueness and geometric descent

This internal derived unit is work of Worker 97 for Task 5397. It derives its claims from
the published group-scheme interfaces and does not assert the quaternionic geometry
required for the task's final statement.

For a form over an arbitrary field, the isometry group is assumed smooth and its
identity component semisimple. The published `simplyConnectedCoverExistence`
then supplies a simply connected central cover of the component. Composing with
the component inclusion gives `IsSpinCover`.

For two spin covers, their factorizations through the component are supplied by
`IsSpinCover.exists_centralIsogeny`. The published
`simplyConnectedCentralCoverUniversalProperty` makes both factorizations into
`IsSimplyConnectedCover` objects. Their canonical isomorphism commutes with the
factorizations and hence with the original maps into the isometry group.
Consequently `IsAlmostSimple.of_iso` and `splitRank_eq_of_iso` transfer almost
simplicity and split rank one from one supplied spin cover to every spin cover.

The companion module `IdentityComponent.AlmostSimpleDescent` descends smoothness
and absolute almost simplicity of an identity component from an actual
group-scheme comparison after any field extension. Applying this to the
isometry group supplies its smoothness and the semisimplicity of its component;
the cover-existence lemma then applies. The comparison model is an arbitrary
smooth affine group with absolutely almost-simple identity component, and is
an explicit hypothesis. In particular, this conditional result does not assert
the existence of the ordinary orthogonal model required by the quaternionic
application.

The Prop-valued `SpinCoverSemisimpleReductionStatement` packages the existence
and isomorphism conclusions under smoothness of the isometry group and
semisimplicity of its component. `spinCoverSemisimpleReduction` proves this
statement at arbitrary universe `u`. There is no local-field, central-division,
quaternionic-dimension, nondegeneracy or Witt-index restriction in these
reductions beyond their explicitly supplied geometric hypotheses.

The missing inputs remain smoothness and semisimplicity for the actual isometry
group, and almost simplicity and split rank one for one cover of the relevant
quaternionic form. No assumption about the characteristic is made in these
reductions. This unit does not prove `LocalSpinRankOneStatement`.
