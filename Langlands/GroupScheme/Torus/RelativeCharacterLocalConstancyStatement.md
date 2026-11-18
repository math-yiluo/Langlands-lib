# Actual relative characters form an abelian étale local system

Worker 616.

`Langlands.GroupScheme.RelativeCharacterLocalConstancyStatement.{u}` is a
Prop-valued statement in every universe. For every scheme `S`, every group
scheme `H` over `S`, and every proof
`hH : RelativeMultiplicativeType.IsMultiplicativeType H`, it asserts

```text
EtaleLocalSystem.IsFinitelyGeneratedLocallyConstant.{u,u} hH.characters.
```

Here `EtaleLocalSystem` abbreviates the namespace
`Langlands.AlgebraicGeometry.EtaleLocalSystem`. The scheme and coefficient
universes are both `u`.

## Actual objects and quantifiers

The published relative multiplicative-type predicate supplies an fppf
cover on which `H` is isomorphic to `D(M)` for finitely generated abelian
groups `M`. These groups may have torsion. No normality, connectedness,
irreducibility, noetherian hypothesis or restriction on the characteristic
is imposed.

The published adapter `hH.commGroupScheme` retains `H` and equips it with
its descended commutative group law. Its `characters` functor is exactly
`Cartier.characters hH.commGroupScheme`, valued in `AddCommGrpCat.{u}` on
`(Over S)ᵒᵖ`. The published `characterHomEquiv` identifies its sections at
`T ⟶ S` with actual homomorphisms `H_T ⟶ Gm_T`. Its maps pull back those
homomorphisms with the canonical base-change comparisons.

The asserted predicate includes sheafness for
`Scheme.etaleTopology.over S`. It also asserts existence of an actual
jointly surjective étale covering family of `S` such that on each member
the restricted presheaf is naturally isomorphic to
`EtaleLocalSystem.constant _ M` for some finitely generated
`M : AddCommGrpCat.{u}`. The coefficient group may vary between cover
members. A constant model has locally constant functions from each test
scheme to the discrete group `M` as sections, with pointwise addition and
pullback of functions as restriction.

The site contains all schemes over `S`; an object's structure morphism
need not be étale. Thus the local trivializations are natural on all
schemes over each covering member.

## Source and formulation

Brian Conrad, *Reductive group schemes* (2014), Proposition B.3.4,
printed pp.290–292, especially p.291, identifies the actual relative
character sheaf of a group of multiplicative type with a locally constant
abelian étale sheaf with finitely generated geometric fibres. The
opening of the proof of Corollary B.3.6, p.293, explicitly reduces normal-base
isotriviality to that sheaf-theoretic assertion.

The registered source is `conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`,
at
`/home/taskhub/central-library/Conrad--Reductive group schemes (SGA3 notes)--2014.pdf`.

The published big-site local-system predicate expresses the source's local
models using actual functors and natural isomorphisms. This statement
asserts that predicate for the published character functor. The
big-site formulation includes arbitrary test schemes and their actual
pullbacks: after étale diagonalization the character presheaf of `D(M)`
is the locally constant-function presheaf with coefficients `M`.
It does not assert the full anti-equivalence in Proposition B.3.4.

## Scope

This module states the character local-constancy result and supplies no
proof. It neither asserts finite étale triviality over normal schemes nor
changes the published normal-base target. It is a prerequisite for that
target's proof.
