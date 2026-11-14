# Étale-local dynamic presentation of a Borel pair

Worker 608.

`Langlands.GroupScheme.RelativeBorelDynamicPresentationStatement.{u}` is a
statement-only, `Prop`-valued definition. This file supplies no proof.

## Meaning and scope

The statement has the same input data and hypotheses as
[`RelativeOppositeBorelStatement`](OppositeBorelStatement.md): an arbitrary
scheme `S`, a reductive group scheme `G`, a relative Borel subgroup `i : B ⟶ G`,
and a maximal torus `t : T.toGrp ⟶ G` contained in `B`. The torus hypotheses
are `RelativeTorus.IsTorus T.toGrp`, `IsClosedSubgroup t` and
`IsFibrewiseMaximalTorus t`. Containment is inclusion of image subgroup
functors on every test scheme.

It asserts that there is an étale cover `𝒰` of `S`. On each member of this
cover, write `G'`, `T'`, `i'` and `t'` for the actual base changes of the given
objects and maps. Then `T'` is split, and there is a cocharacter `ν` of `T'`
such that, for `χ := ν ≫ t'`:

- the image of the given base-changed Borel `i'` is `Dynamic.parabolic χ`;
- `Dynamic.centralizer χ` is the image of the given base-changed torus `t'`;
- an actual relative Borel subgroup `iminus : Bminus ⟶ G'` has image
  `Dynamic.parabolic (Dynamic.oppositeCocharacter χ)`.

The equalities are of subgroup functors on all test schemes over the cover
member. The last clause includes the complete
`IsRelativeBorelSubgroup iminus` predicate, not only Borelness of its fibres.
There is no affineness, reducedness, connectedness or Noetherian assumption
on the base, and the torus need not be split before passing to the cover.

## Provenance

This is a derived local construction extracted from Brian Conrad,
*Reductive group schemes* (2014), registered as
`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
The one-based PDF pages agree with the printed pages.

Proposition 5.2.3, pp.152–153, presents a specified parabolic containing a
specified split maximal torus locally as `P_G(λ)`, after splitting the pair
étale-locally and then refining Zariski-locally. The proof of Proposition
5.2.12, p.158, applies this construction to a Borel subgroup, identifies
`Z_G(λ)` with the given torus, and takes `P_G(−λ)` as a Borel subgroup.
Definition 5.2.10, p.157, supplies the relative Borel convention.

The Library uses `CommGroupScheme.groupHom` to regard a torus cocharacter
as a group-scheme homomorphism. `Dynamic.oppositeCocharacter` precomposes
with inversion on `Gm`, so it encodes `−λ`. A sequence of étale and open
refinements is expressed here as a single étale cover. All maps in the
conclusion are the actual categorical base changes of the original maps.

## Relation to the opposite Borel target

This statement isolates local dynamic presentation and representability
of the negative dynamic Borel. It does not assert the intersection formula,
uniqueness, or descent of the local negative Borels. Those remain proof
obligations for `RelativeOppositeBorelStatement`.
