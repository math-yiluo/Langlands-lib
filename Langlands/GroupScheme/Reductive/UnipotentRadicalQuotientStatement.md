# The pseudo-reductive quotient by a ground-field unipotent radical

`Langlands.GroupScheme.UnipotentRadicalQuotientStatement.{u}` is a
Prop-valued statement for every universe `u`. It quantifies over every
field `k : Type u` and actual group scheme `G` over
`Spec (CommRingCat.of k)` with `Smooth G.X.hom`,
`IsAffineHom G.X.hom`, and `ConnectedSpace G.X.left`. For every actual
group scheme `U` over that base and homomorphism `i : U ⟶ G` satisfying
the published `IsUnipotentRadical i`, it asks for an actual group scheme
`Q` over the same base and a homomorphism `q : G ⟶ Q` with

- `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q`;
- `IsPseudoReductive Q`.

The quotient predicate is reused unchanged from
`Langlands.GroupScheme.Rational.RootSubgroupStructureStatement`. It
requires the underlying scheme map of `q` to be flat, surjective, and
locally of finite presentation, and the equality
`SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i`.
Thus the specified kernel is the image of the actual scheme kernel on
every relative test scheme, including nonaffine and nonreduced tests.
This expresses the represented fppf quotient; the statement imposes no
surjectivity on the point group of each original test scheme or on
ground-field rational points.

The existing `IsPseudoReductive Q` has four fields: `Smooth Q.X.hom`,
`IsAffineHom Q.X.hom`, `ConnectedSpace Q.X.left`, and
`HasTrivialUnipotentRadical Q`. The last says that every smooth connected
unipotent normal closed ground-field subgroup has trivial all-test image.
Accordingly the conclusion includes smoothness, connectedness,
affineness, and ground-field radical triviality. It uses an actual quotient
group scheme, with its group structure and homomorphism, rather than only
a quotient scheme.

The supplied radical is the ground-field radical `R_{u,k}(G)`. Its
published predicate includes greatest containment among smooth connected
unipotent normal closed subgroups over `k` itself. The split ground-field
radical restricts that class by splitness, while the geometric radical is
taken after base change to an algebraic closure. Quotienting by the
ground-field radical is the conclusion here. Over an imperfect field,
pseudo-reductivity does not assert triviality of the geometric radical.
No perfectness, characteristic, algebraic-closure or reductivity
hypothesis is imposed.

The source is Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second
edition (2015), Definition 1.1.1, printed p.3 (PDF p.29), for the radical
and pseudo-reductive notions, and Remark 1.1.4, printed p.5 (PDF p.31),
for the assertion that `G/R_{u,k}(G)` is pseudo-reductive and the resulting
extension structure. The represented fppf quotient and exact all-test
kernel formulate this quotient assertion using the Library's existing
interface. Registered source:
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
Printed page `p` is PDF page `p + 26`. No project errata file for this
source was present when this statement was prepared.

This file defines a proposition and supplies no quotient construction or
proof of pseudo-reductivity. Its radical hypothesis characterizes the
supplied subgroup; it assumes no radical-existence or quotient theorem.
Existence of a radical has a separate statement module.
