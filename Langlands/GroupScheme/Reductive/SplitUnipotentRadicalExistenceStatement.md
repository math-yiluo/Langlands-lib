# Existence of the split ground-field unipotent radical

`Langlands.GroupScheme.SplitUnipotentRadicalExistenceStatement.{u}` is a
Prop-valued statement for every universe `u`. For every field `k : Type u`
and actual group scheme `G` over `Spec (CommRingCat.of k)` with
`Smooth G.X.hom`, `IsAffineHom G.X.hom`, and
`ConnectedSpace G.X.left`, it asks for an actual group scheme `V` over the
same base and homomorphism `j : V ⟶ G` satisfying the published
`IsSplitUnipotentRadical j`.

This predicate is imported unchanged from
`Langlands.GroupScheme.Reductive.UnipotentRadical`. It requires a closed
immersion, smoothness and connectedness of `V`, `IsUnipotent V`,
`RelativeRoot.IsSplitUnipotent V`, and normality of
`SubgroupFunctor.range j`. Its greatestness condition contains every
smooth connected split unipotent normal closed ground-field subgroup.
Images, normality and containment are tested on all schemes over the
base, including nonaffine and nonreduced tests.

The splitness condition reuses the existing finite
`RelativeRoot.HasSplitSeries` predicate: the endpoint is trivial, and
each step has a smooth connected normal closed kernel and a represented
fppf quotient whose all-test point functor is naturally the
one-dimensional additive group. The statement supplies existence of a
representative satisfying this predicate; it introduces no second
definition of splitness.

The split ground-field radical `R_{us,k}(G)` differs from the ground-field
radical `R_{u,k}(G)`, whose defining class includes unipotent subgroups
without a splitness requirement. The geometric radical belongs to the
base change to an algebraic closure. These distinctions are retained
over imperfect fields. The statement makes no identification of these
three notions and places no perfectness, characteristic, algebraic-closure
or reductivity restriction on its inputs.

The source is Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second
edition (2015). The discussion preceding Proposition 2.2.4, printed p.63
(PDF p.89), defines the maximal split smooth connected unipotent normal
ground-field subgroup and explicitly asserts its existence. The published
predicate expresses its canonical maximality as greatest image
containment. Corollary B.3.5, printed p.574 (PDF p.600), identifies this
split radical with the split part of `R_{u,k}(G)` from Theorem B.3.4,
printed pp.573–574 (PDF pp.599–600). That characterization motivates
the target but is not included in it. In particular, the target does not
also assert a wound quotient or compatibility with separable extension.
Definition 1.1.1, printed p.3 (PDF p.29), supplies the ground-field
radical for this comparison.

Registered source: `conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
Printed page `p` is PDF page `p + 26`. No project errata file for this
source was present when this statement was prepared.

The file defines a proposition and supplies no proof or chosen split
radical. The source's existence and characterization results are not
available as Lean theorems merely from this declaration.
