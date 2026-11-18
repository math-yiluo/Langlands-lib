# Semisimple representations and the identity component over a field of characteristic zero

This module is internal supporting work for the proof of
`Langlands.GroupScheme.CharZeroSemisimpleRepresentationIdentityComponentStatement`. It proves
both directions of Milne's Corollary 22.43 over an arbitrary field of characteristic zero by
base change to `AlgebraicClosure k`, assuming Milne's Proposition 4.19 in the form of the
published statement `SemisimpleRepresentationFieldExtensionStatement` (hypothesis `h419`) and,
for one direction, Theorem 22.42 in the form of `CharZeroReductiveSemisimpleRepresentationStatement`
(hypothesis `h22`).

## Base change of closed subgroups

`isClosedSubgroup_baseChange`: for any field `k`, any commutative ring `R'` and any morphism
`b : Spec R' ⟶ Spec k`, the base change `ψ.baseChange b` of a closed-subgroup matrix
representation is a closed subgroup. It is the base change of `ψ` (published
`IsClosedSubgroup.baseChange`) followed by the isomorphism `GeneralLinear.baseChangeIso`.

## Setting

Now `k` has characteristic zero and `G` is a group scheme over `Spec k` with
`[LocallyOfFiniteType G.X.hom]`, `[IsAffineHom G.X.hom]` and `[Smooth G.X.hom]`.
`geometricGroup G` abbreviates the base change of `G` along `toAlgebraicClosure k`; it is smooth
and affine (instances of `IdentityComponent`), hence locally of finite type and, by
`isReduced_geometricGroup`, reduced.

## Results

- `isSemisimpleStable_of_geometric_rational h419 ρ`: if the base change
  `ρ.baseChange (toAlgebraicClosure k)` has semisimple rational-point representation, then
  `ρ.IsSemisimpleStable`. By `isSemisimpleStable_iff_rationalRepresentation` (module
  `RationalBridge`) the base change is semisimple; the descent conjunct of `h419` (Milne 4.19:
  semisimplicity after extension implies semisimplicity) concludes. Here `ρ` has any finite index
  type.
- `geometric_rational_of_isSemisimpleStable h419 ρ`: conversely, if `ρ.IsSemisimpleStable` then
  the base change has semisimple rational-point representation. It uses the ascent conjunct of
  `h419` with the separability of `AlgebraicClosure k` over the characteristic-zero field `k`.
- `isSemisimpleStable_of_identityComponent h419 hG ρ` (**Milne 22.43, "if"**): if
  `IsConnectedReductive (identityComponent G)` then every matrix representation `ρ` (any finite
  index type) satisfies `ρ.IsSemisimpleStable`. The base change of the identity component is
  connected reductive (published `connectedReductiveFieldExtensionStatement`) and is identified
  with the identity component of `geometricGroup G` by the published
  `IdentityComponent.baseChangeIso` and `IsConnectedReductive.of_iso`; it is pseudo-reductive
  (`IsConnectedReductive.isPseudoReductive`), so
  `rationalRepresentation_isSemisimple_of_identityComponent` (module `AlgClosedCore`) applies to
  `ρ.baseChange (toAlgebraicClosure k)`.
- `identityComponent_isConnectedReductive h22 h419 h` (**Milne 22.43, "only if"**): if every
  `ρ : MatrixRepresentation G (Fin N)` satisfies `ρ.IsSemisimpleStable`, then
  `IsConnectedReductive (identityComponent G)`. A closed-subgroup representation `ψ` exists by the
  published `affineLinearEmbeddingStatement`; its base change is a closed subgroup with semisimple
  rational-point representation; `identityComponent_isConnectedReductive_of_faithful`
  (module `AlgClosedCore`) makes the identity component of `geometricGroup G` connected
  reductive; `IdentityComponent.baseChangeIso` transfers this to the base change of
  `identityComponent G`, and the published `IsConnectedReductive.of_fieldExtension` descends it to
  `identityComponent G`.

## Provenance

Internal and derived. The source assertions are Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups`: Corollary 22.43 (printed p. 478, PDF p. 494), Theorem 22.42
(printed p. 477) and Proposition 4.19 (printed pp. 90–91). Milne also passes to `k^a` in his
proof of 22.43 "if"; the reduction to an algebraically closed field through Proposition 4.19 is
the route chosen here.
