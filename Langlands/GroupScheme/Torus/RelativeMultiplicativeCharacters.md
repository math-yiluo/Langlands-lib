# Actual relative characters of groups of multiplicative type

This is an internal adapter for the published arbitrary-base predicates in
`RelativeMultiplicativeType` and the actual character functor in
`Cartier.Characters`. It applies to every scheme `S` and every group scheme `H`
with an fppf diagonalizing cover by finitely generated abelian models, including
models with torsion.

`IsDiagonalizable.isCommMonObj` transports the commutative law of the
diagonalizable model along its group-scheme isomorphism. The model is the base
change of a commutative diagonalizable group from `Spec ℤ`.
`IsMultiplicativeType.isCommMonObj` applies the published
`isCommMonObj_of_fppfCover` to the diagonalizing cover. This proof uses the
faithfulness of restriction of actual group-valued points along that cover.

`IsMultiplicativeType.commGroupScheme` keeps the underlying group scheme and
records the descended commutativity proof. Its underlying `GroupScheme` is
definitionally `H`, and it commutes with arbitrary base change; the latter
equality uses proof irrelevance for the commutativity fields.

`IsMultiplicativeType.characters` is exactly `Cartier.characters` applied to
this commutative group scheme. It is an actual functor
`(Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}` for `S : Scheme.{u}`. Its value on `T ⟶ S`
identifies additively with group-scheme homomorphisms from `H_T` to `Gm_T`,
through `IsMultiplicativeType.characterHomEquiv`. The restriction compatibility
lemma is the published `Cartier.characterHomEquiv_restrict`, so the maps are
base change of actual homomorphisms with the canonical pullback comparisons.
The character group is written additively, as in `Cartier.Characters`.

These constructions are derived from the imported definitions and proved
fppf commutativity descent; they add no local constancy or finite-cover
triviality hypothesis. They do not prove the étale local constancy of the
character functor or the normal-base isotriviality statement.

The shared fppf-locality and commutativity declarations are provided by
`RelativeMultiplicativeTypeLocality`; this module imports and reuses them.
