# Existence of the ground-field unipotent radical

`Langlands.GroupScheme.UnipotentRadicalExistenceStatement.{u}` is a
Prop-valued statement for every universe `u`. For every field `k : Type u`
and every actual group scheme `G` over `Spec (CommRingCat.of k)` with
`Smooth G.X.hom`, `IsAffineHom G.X.hom`, and
`ConnectedSpace G.X.left`, it asks for an actual group scheme `U` over the
same base and a homomorphism `i : U ⟶ G` satisfying the published
`IsUnipotentRadical i`.

The imported predicate from
`Langlands.GroupScheme.Reductive.UnipotentRadical` requires a closed
immersion, smoothness and connectedness of `U`, the existing `IsUnipotent U`,
and normality of `SubgroupFunctor.range i`. Its greatestness condition
contains the image of every smooth connected unipotent normal closed
ground-field subgroup. Images, normality and containment are tested on all
schemes over the base, including nonaffine and nonreduced tests. The
statement reuses this predicate unchanged and adds the existence
quantifiers that the predicate alone does not supply.

This is the ground-field radical `R_{u,k}(G)`. The split ground-field
radical additionally requires `RelativeRoot.IsSplitUnipotent`, restricting
both the representative and its competitors to the split class. The
geometric radical is taken after extending the ground field to an
algebraic closure. These notions can differ over imperfect fields; the
statement asserts neither splitness nor equality with the geometric
radical after base change. It places no perfectness, characteristic,
algebraic-closure or reductivity restriction on `k` or `G`.

The source is Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second
edition (2015), Definition 1.1.1, printed p.3 (PDF p.29). That definition
describes the canonical maximal smooth connected unipotent normal
ground-field subgroup. The published predicate expresses its canonical
maximality as greatest image containment; this declaration states
existence in that precise form. The discussion on printed pp.4–5
(PDF pp.30–31) explains the distinction from the geometric radical.
Registered source: `conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
Printed page `p` is PDF page `p + 26`. No project errata file for this
source was present when this statement was prepared.

The file defines a proposition and supplies no proof or chosen radical.
Quotient structure and split radical existence have their own separately
reusable statement modules.
