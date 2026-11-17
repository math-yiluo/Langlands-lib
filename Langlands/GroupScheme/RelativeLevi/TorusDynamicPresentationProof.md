# Étale local dynamic presentations along a prescribed maximal torus

Worker 189.

`Langlands.GroupScheme.relativeTorusDynamicPresentation` proves the unchanged
`Langlands.GroupScheme.RelativeTorusDynamicPresentationStatement.{u}` for
every universe `u`.

For an arbitrary scheme `S`, a reductive group scheme `G/S`, a relative
parabolic inclusion `i : P ⟶ G`, and a prescribed closed relative torus
`t : T.toGrp ⟶ P` maximal on every residue-field fibre of `P`, the theorem
gives an étale cover of `S`. On each member, a cocharacter of the direct
pullback of that same `T`, composed with the pullbacks of `t` and `i`,
dynamically presents the actual pulled-back inclusion `i`. Its
`IsRepresentedBy` certificate includes monomorphy and equality of subgroup
functors on every test scheme, including nonreduced tests.

The implemented proof applies the published construction
[`RelativeLevi.torusDynamicPresentationCover`](TorusDynamicCover.md) to the
given data. This returns a dependent pair consisting of a small étale cover
and a `TorusDynamicPresentation` on every member. The proof takes that cover
and, for each member, the presentation's `cocharacter` and `represents`
fields. These have exactly the types required by the published statement.
The constructor already works without the separate closedness premise on
`t`; the theorem retains that premise as required by its unchanged target.
No further hypotheses or supplied cocharacters are introduced.

The imported construction splits the prescribed relative torus on an étale
cover, transports its fibrewise maximality into the reductive ambient group,
and chooses open dynamic presentation neighbourhoods through that split
torus. It binds these neighbourhood covers to the splitting cover.
Canonical pullback comparison isomorphisms transport the cocharacters and
their full representation certificates from iterated to direct pullbacks.
The present proof only extracts this already constructed data.

This is an internal composition of published Library results. Its original
geometric source is Brian Conrad, *Reductive group schemes* (2014),
Proposition 5.2.3 and its proof, pp.152–153; the prescribed-torus presentation
is used in the proof of Proposition 5.4.5, p.177. The registered source is
`conrad-2014-reductive-group-schemes`,
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
These are both printed and one-based PDF page numbers. The target statement
and all its imports are unchanged. The conclusion is local; it supplies
neither a global cocharacter nor a Levi subgroup or descent construction.
