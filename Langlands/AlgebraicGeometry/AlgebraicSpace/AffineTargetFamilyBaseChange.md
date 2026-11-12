# Actual field fibres of target families after scheme base change

This internally derived supporting unit compares actual fibre point topologies.
It imposes no affine, finiteness, separation or representability assumption on
the morphism of algebraic spaces. All tests can be arbitrary schemes in the
declared universe, and therefore include the field tests in the published
geometrically connected fibre predicate.

`restrictedBaseIsTerminal` applies preservation of the terminal object by
presheaf restriction to the represented original base. `restrictedBaseIso`
uses uniqueness of terminal objects to identify it with the represented new
base, and lifts that presheaf isomorphism to algebraic spaces.

`structuralBaseChangeFibreHomeomorph g X t` identifies the actual structural
fibre of the base change of X along g, tested by a scheme map t into the new
base, with the original structural fibre tested by t followed by g. The
proof compares the structural morphism with the base change of the original
structural morphism using the terminal target isomorphism. It composes the
resulting fibre isomorphism with the existing fibre restriction homeomorphism.
Uniqueness of maps to the original terminal base identifies the recovered test.

For a target chart b from V and a represented test r into V,
`AffineTargetFamily.testFibreHomeomorph` identifies the structural fibre of
`AffineTargetFamily.space f b` over the underlying scheme map of r with the
original fibre of f over the composite of the Yoneda image of r and b.
It uses the actual rebase fibre homeomorphism, recovers the original represented
test through its identity-on-schemes comparison, and pastes the two actual
pullback squares. No fibre property is postulated for either family.

`AffineTargetFamily.originalBaseChart_restrictAtlas` identifies a represented
test of the restricted chart with its original test under the slice
map/pullback adjunction. This is the Yoneda evaluation identity for the
existing chart restriction and scheme base-change isomorphism.

The provenance is composition of existing Library constructions and proofs.
This unit supplies the topological comparisons for connected-fibre descent;
it does not yet assert the equivalence of connected-fibre predicates after
base change, eventual descent for arbitrary morphisms, or the full eight-property
host statement.
