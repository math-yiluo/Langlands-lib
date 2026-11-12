# Descent from an actual standard symplectic model

Author: Worker 118.

`Langlands.GroupScheme.Symplectic.AlgebraicModel G n` packages an algebraic
extension `L/K` and an actual group-scheme isomorphism

`G_L ≅ Symplectic.groupScheme L n`.

Both fields have the same arbitrary universe `u`. The extension need not be
finite or separable. This is a data structure. It neither asserts the existence
of such a model nor supplies one for any quaternionic form.

Every theorem in the module takes `Symplectic.StructureStatement.{u}` and
`2 ≤ n` as explicit premises. The standard structural statement is a separate
proof obligation.

- `AlgebraicModel.isSimplyConnected` transports simple connectedness from
  standard `Sp_{2n}` to `G_L` by `IsSimplyConnected.of_iso`, then applies the
  published `IsSimplyConnected.of_algebraicExtension` from
  `SimplyConnected.AlgebraicExtensionReflection`.
- `AlgebraicModel.isAbsolutelyAlmostSimple` transports absolute almost-simplicity
  by `IsAbsolutelyAlmostSimple.of_iso`, then reflects it along the field
  extension using `IsAbsolutelyAlmostSimple.of_fieldExtension` from
  `SimplyConnected.AlmostSimpleFactorDescentProperties`. This reflection does
  not itself require the extension to be algebraic.
- `isConnectedReductive` extracts connected reductivity from semisimplicity,
  which is part of simple connectedness.
- `isSimplyConnected_and_isAlmostSimple` combines the two structural conclusions
  needed in the local quaternionic rank-one statement.

The provenance is internal: the module composes the published isomorphism and
field-extension transport results on supplied data. The actual splitting/Morita
model of a quaternionic group, the standard symplectic structural theorem, and
the rational split-rank calculation remain separate obligations.
