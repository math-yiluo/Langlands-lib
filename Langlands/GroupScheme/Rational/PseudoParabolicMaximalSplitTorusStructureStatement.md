# Maximal split tori and the minimality criterion for pseudo-parabolics

Author: Worker 274.

`Langlands.GroupScheme.PseudoParabolicMaximalSplitTorusStructureStatement.{u}`
states the maximality observation immediately before Proposition C.2.4
and the proposition itself in Conrad–Gabber–Prasad, *Pseudo-reductive
groups*, second edition (2015), printed pp.594–595 (PDF pp.620–621).
The registered source is `conrad-gabber-prasad-2015-pseudo-reductive`,
SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
This is an unproved proposition definition.

Let `G` be any smooth connected affine group scheme over any field
`k : Type u`, let `i : P ⟶ G` be pseudo-parabolic, and let
`s : S.toGrp ⟶ P` be an actual maximal split torus of `P`.
The statement asserts three conclusions:

1. The composite `s ≫ i` is a maximal split torus of `G`.
2. The whole-torus centralizer `torusCentralizer (s ≫ i)` is contained
   in `SubgroupFunctor.range i` on every relative scheme test.
3. For every actual representative `j : U ⟶ P` of the split ground-field
   unipotent radical of `P`, minimality of `i` is equivalent to
   `i` representing the fppf-local product of that centralizer and the
   ambient image `SubgroupFunctor.range (j ≫ i)`.

The first conclusion is the maximality observation just before the
proposition. It transfers maximality from `P` to `G`. The existing reverse
transfer, from an ambient maximal split torus to a containing closed
subgroup, does not supply this assertion.

The second and third conclusions express `Z_G(S) ⊆ P` and
`P = Z_G(S) · R_us,k(P)` from Proposition C.2.4. The centralizer predicate
tests commutation after every refinement of every relative scheme test.
The product predicate requires closedness and equality of membership
on every test with an ordered product after a flat surjective locally
finitely presented relative cover. This allows products that do not
factor on the original test. It retains the subgroup-scheme meaning of
the source's product equality.

The supplied `IsSplitUnipotentRadical j` includes smoothness,
connectedness, unipotence, the actual split-unipotent series, all-test
normality and greatestness among such normal closed subgroups of `P`.
It is distinct from the possibly nonsplit ground-field unipotent radical
in the definition of a pseudo-parabolic. The statement is independent of
the choice of representative: it quantifies over every such `U,j`.
Existence of a represented split radical is a separate prerequisite;
this statement neither asserts that existence nor chooses a radical.

Minimality is exactly the published
`IsMinimalPseudoParabolicSubgroup i`, comparing all ground-field
pseudo-parabolic subgroup images on all relative tests. There is no
reductivity, pseudo-reductivity, perfection, characteristic, infinitude
or splitting restriction on the field or ambient group. The field, group
schemes and test schemes have arbitrary universe `u`.

The source proof uses C.2.3 and earlier quotient, radical and wound-group
action results. This statement supplies no proof of those inputs or of
the criterion. In particular, it does not use the later minimal
pseudo-parabolic conjugacy theorem C.2.5 as an assumption.
