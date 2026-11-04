# The central additive-subgroup criterion for unipotent woundness

Author: Worker 1478.

`UnipotentWoundCriterionStatement.{u}` is a Prop-valued all-field analogue
of the equivalence of conditions (1) and (2) in Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, second edition (2015), Proposition B.3.2,
printed p.572, one-based PDF p.598. The registered source is
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
The affine-line constancy formula is Definition B.2.1, printed p.568,
PDF p.594. The full equivalence is unproved in this file.

Appendix B has the standing assumption of positive characteristic,
explicit on printed p.561, PDF p.587. Thus B.3.2 supplies the
positive-characteristic source statement. Extending the criterion to
characteristic zero is part of this derived target, not a claim about
the scope of B.3.2. In characteristic zero the intended route uses the
last nontrivial descending central-series term and the classification
of commutative unipotent groups as vector groups; neither classification
nor this reverse implication is supplied here. CGP A.1.4, printed p.467,
PDF p.493, supplies the related splitness result over perfect fields.

For every field `k : Type u` and every smooth connected affine unipotent
actual group scheme `G` over `Spec k`, the target says that
`HasConstantAffineLineMaps G` holds if and only if there is no actual
central closed subgroup `j : V ⟶ G` whose group is a one-dimensional
vector group. The field is unrestricted: it need not be perfect, infinite
or algebraically closed, and either characteristic is allowed.

The constancy condition quantifies over actual `k`-scheme morphisms from
the affine line and requires each to factor through the terminal object
of `Over (Spec k)` at an existential rational value. It concerns all such
morphisms, without a group-homomorphism requirement.
`IsClosedSubgroup j` requires the underlying scheme morphism to be a
closed immersion. `IsCentral j` is the existing all-test, all-refinement
center condition. `RelativeRoot.IsVectorGroupOfDimension V 1` gives natural
group equivalences between the points of `V` and the additive group of one
global function on every relative scheme test. These coordinates give an
actual group-scheme isomorphism with the one-dimensional vector group;
they express the source's requirement that the subgroup be `k`-isomorphic
to `Ga`. No rational-point-only surrogate or assumption about lifts on
each test is used.

The existing `IsUnipotent` predicate, defined through actual finite
representations and their fixed vectors, is retained unchanged. A proof
must justify the source's structural unipotent-group arguments for this
predicate. No comparison with another unipotence definition is a premise.
The theorem's other conclusions concerning separable extensions and the
cckp-kernel are outside this statement.

Two unconditional elementary lemmas accompany the target.
`HasConstantAffineLineMaps.not_isVectorGroupOfDimension_one_closed_subgroup`
uses the existing vanishing theorem for homomorphisms from one-dimensional
vector groups. Constancy makes the given inclusion the zero homomorphism.
Positive-dimensional vector coordinates provide a nonidentity rational
point, while the inclusion's monomorphism forces that point to be the
identity, a contradiction.
`not_exists_central_additive_closed_subgroup` packages this contradiction
as the forward implication. Neither lemma needs centrality, smoothness,
affineness, connectedness or unipotence of the ambient group.

The missing reverse implication is the substantive part of B.3.2.
Its source proof uses the central commutative `p`-torsion subgroup and
B.2.5–B.2.6, after reducing a nonconstant affine-line map to that subgroup.
Defining this target or proving its forward implication does not establish
that construction. It also does not prove the split-part theorem B.3.4,
radical-quotient woundness B.3.5, or pseudo-parabolic rational lifting.
