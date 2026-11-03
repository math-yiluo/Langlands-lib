# Central equivariant vector subgroups and smooth unipotent quotients

This pair states two geometric prerequisites for the dimension induction in
Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition (2015), Theorem
3.3.11, printed pp.114–116, particularly p.115 (PDF pp.140–142). The registered
source is `conrad-gabber-prasad-2015-pseudo-reductive`, SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
These are Prop-valued statement definitions. This file proves neither
prerequisite nor the semigroup ordered-product theorem.

`IsLinearVectorCoordinates` is the coordinate expression of an equivariant
linear structure in CGP A.1.1, printed p.466 (PDF p.492), and B.4.3, printed
p.576 (PDF p.602). It requires the existing `IsNaturalVectorCoordinates`:
on every scheme over the field, points are identified multiplicatively with the
additive group of `n` global functions, naturally under every test morphism.
For every acting point and every scalar in that test's ring of global functions,
the action commutes with scalar multiplication transported through those
coordinates. Additivity is already supplied by `AutomorphicAction` and the
coordinate group equivalences. Thus each action is linear over the actual
global-function ring. No choice of a single weight is imposed; distinct weights
and zero weights are permitted.

`CentralStableVectorSubgroupStatement` has the following scope and outputs.
For every algebraically closed field in the arbitrary universe `u`, let `G` be
a smooth connected affine unipotent group, nontrivial as an all-test subgroup
functor, and let a split torus `S` act through an actual `AutomorphicAction`.
It asks for an actual closed inclusion `z : Z ⟶ G`, an actual action on `Z`,
and natural linear vector coordinates of positive finite dimension `n`.
The subgroup is smooth, connected, affine, unipotent, central, stable, and
nontrivial. Centrality is the Library's `IsCentral`, which tests membership in
the center on every scheme and every refinement. Stability concerns the actual
all-test range of `z`. Inclusion equivariance is required on every test, and
`SmoothOfRelativeDimension n Z.X.hom` ties the coordinate dimension to the
scheme dimension used by the quotient statement.

This scope follows the order of CGP's proof: first pass to an algebraically
closed field and reduce to a unipotent group. The last nontrivial descending
central-series term is central and stable. In characteristic zero it supplies
the required vector group. In positive characteristic take its last nonzero
power-of-`p` image to obtain a smooth connected commutative `p`-torsion group.
CGP B.1.10, printed p.565 (PDF p.591), makes it a vector group over an
algebraically closed field. CGP B.4.3, printed pp.576–577 (PDF pp.602–603),
supplies an equivariant linear structure: its fixed part is also a vector
group by B.1.10, and the complementary part has a linear torus action. The
statement does not assert existence of this subgroup over every ground field.

`CentralSmoothQuotientStatement` starts with a given smooth connected closed
central subgroup and its actual equivariant inclusion, over any field in
universe `u`. The ambient group is smooth connected affine and unipotent. Given
smooth relative dimensions `d` for `G` and `n > 0` for `Z`, it asks for a genuine
smooth connected affine unipotent group scheme `Q`, a homomorphism `q : G ⟶ Q`,
and an actual descended torus action on `Q`. Its kernel is exactly the range
of `z` as a subgroup functor. More precisely, the existing `IsFppfQuotient`
requires flatness, surjectivity and local finite presentation of the scheme
map and equality between that range and the range of the actual scheme
kernel inclusion. The map is additionally smooth of relative dimension `n`.
The quotient has smooth relative dimension `m`, with `d = n + m` and `m < d`.
Quotient equivariance is imposed on every test scheme. No surjectivity on
points of each original test scheme is assumed or concluded.

The quotient formulation packages CGP A.1.11, printed p.470 (PDF p.496),
together with the smooth quotient and strict dimension decrease used on
printed p.115. A.1.11 describes the group-scheme quotient by a normal subgroup,
its exact kernel, and preservation of smoothness and affineness in this
situation. Centrality makes the specified subgroup normal; the equivariant
inclusion makes it stable, so the action descends. Each quotient fiber is an
fppf-local translate of `Z`, which explains the relative dimension `n`;
composition gives `d = n + m`. Positivity of `n` yields the strict decrease.
This last dimension equation and the explicit all-test equivariance are
derived interface expressions of the source's quotient construction, not
additional claims that the source prints in this syntax.

CGP A.1.3, printed p.467 (PDF p.493), records preservation of unipotence by
quotients, using a geometric additive-group-series characterization. The
Library's `IsUnipotent` instead quantifies over actual finite matrix
representations and their all-test fixed vectors. Both statement components
retain that existing Library predicate. A proof must justify the structural
steps for that predicate, including any comparison with the source's
characterization; the declaration supplies no such comparison as a premise or
as an established result.

`CentralVectorQuotientStatement` is exactly the conjunction of these two
targets, at every universe `u`. The split-torus restriction in the quotient
component keeps it within the intended application. Smooth relative
dimensions use Mathlib's standard-smooth-chart predicate, avoiding an assumed
identification with a Lie-algebra rank. There is no semigroup product conclusion
or geometric-point criterion in these definitions. The exact original
cross-exclusion, zero-weight conventions, arbitrary ordering, empty case,
base-change descent, and final ordered-multiplication argument remain
obligations of the separate semigroup ordered-product proof.
