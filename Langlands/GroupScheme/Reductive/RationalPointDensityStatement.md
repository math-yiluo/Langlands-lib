# Zariski density of rational points of connected reductive groups

`Langlands.GroupScheme.ReductiveRationalPointDensityStatement` states that, for
every infinite field `k : Type u` and every actual connected reductive group
scheme `G` over `Spec k`, the union of the images of its `k`-rational points is
dense in the underlying topological space of `G`.

The topology here is the Zariski topology of the scheme. A rational point is an
actual morphism from the identity object of `Over (Spec k)` to `G.X`, using the
published `RationalPoint` convention. Thus `Set.range p.left` is its image in
the underlying scheme, and the displayed union denotes the usual set of
`k`-rational points inside that space. No topology on the field is chosen.

The connected reductive hypothesis is the existing
`IsConnectedReductive G`: smoothness, affineness, connectedness, and trivial
geometric unipotent radical. The statement allows imperfect infinite fields,
nonsplit groups, and the trivial group, at arbitrary universe `u`.

The source is J. S. Milne, *Algebraic Groups* (2017), Theorem 17.93(b),
printed page 382 (PDF page 398): a reductive group is unirational, and its
rational points over an infinite field are Zariski dense. The registered
2026-11-02 errata snapshot has no correction to this assertion. This module
records the density consequence as a proposition; it supplies no proof.
