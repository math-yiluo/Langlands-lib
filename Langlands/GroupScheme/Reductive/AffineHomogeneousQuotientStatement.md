# Reductivity from an affine homogeneous quotient

Author: Worker 1471.

`Langlands.GroupScheme.AffineHomogeneousQuotientReductiveStatement.{u}`
is a Prop-valued statement, with no proof supplied in this module. It asserts
that a smooth closed subgroup of a connected reductive group over any field
has connected reductive identity component if an actual affine homogeneous
quotient is supplied.

The statement quantifies over a field `k : Type u`, an actual group scheme
`G` over `Spec (CommRingCat.of k)` with `IsConnectedReductive G`, an actual
group scheme `H`, a homomorphism `i : H ⟶ G` with `IsClosedSubgroup i`, and
`Smooth H.X.hom`. It derives affineness of `H` by composing its closed
immersion with the affine structural map of `G`. These instances make the
published `identityComponent H` available. It does not assume `H` connected
or reductive.

The supplied quotient is exactly
`HomogeneousQuotientFromEmbedding.HomogeneousQuotient i`, imported from
`Langlands.GroupScheme.HomogeneousQuotientFromEmbedding`. This existing
structure contains a scheme `Q.scheme` over `Spec k`, a morphism
`Q.projection : G.X ⟶ Q.scheme`, separatedness, local finite type and
quasi-compactness of the quotient, and smoothness, surjectivity and
quasi-compactness of the projection. Its `fibers` field requires, for every
scheme `T` over `Spec k` and every pair `g h : T ⟶ G.X`,

```text
g ≫ Q.projection = h ≫ Q.projection
  ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T.
```

Thus the quotient has the actual right-coset fibers on every scheme test,
including nonaffine and nonreduced tests. Smooth surjectivity supplies local
lifts in the fppf topology; it does not assert a lift over each original test
scheme or on every group of rational points. No new quotient interface is
introduced here. The additional hypothesis `IsAffineHom Q.scheme.hom` says
that this actual quotient is affine over the field.

The conclusion is the existing `IsConnectedReductive (identityComponent H)`.
It includes smoothness, affineness, connectedness and triviality of the
geometric unipotent radical. In particular, it is stronger than a claim about
the ground-field unipotent radical over an imperfect field. There is no
restriction on characteristic, perfectness, or the universe `u`.

The source is Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition
(2015), the proof of Proposition A.8.12, printed pp.552–553 (PDF pp.578–579).
After extending the ground field to its algebraic closure, that proof states
the criterion for the identity component of an arbitrary smooth closed
subgroup and refers to `[Bo1, Thm. 1.1(i)]` or `[Ri, Thm. A]` for its proof.
The arbitrary-field formulation here is the descended criterion: extend an
affine quotient to the algebraic closure and use the compatibility of the
actual identity component with field extension. The imported
`IdentityComponent.baseChangeIso` supplies that comparison; this module does
not prove the geometric criterion or the descent argument. The quotient
structure spells out the represented quotient meant in that passage.
Registered source: `conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
No project errata file for this source was found when preparing the statement.

This generic criterion is a prerequisite for proving reductivity of full
character-kernel centralizers. It supplies neither existence nor affineness
of those quotients, and it asserts no fixed-subgroup theorem. Those
constructions, the application to the full possibly nonreduced kernel, and
an actual proof of this criterion remain separate proof obligations.
