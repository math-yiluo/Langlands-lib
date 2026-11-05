# Finite étale splitting of actual generic-fibre components

`Langlands.AlgebraicGeometry.SchemeFiberGeometry.finiteTypeFiniteEtaleGenericComponentSplitting`
proves the published proposition
`FiniteTypeFiniteEtaleGenericComponentSplitting.{u}` in an arbitrary common
universe `u`. Its mathematical source is Stacks Project Lemma 37.24.8
(0551), in the registered collection
`stacks-generic-geometric-irreducibility-2026-11-04`, file `0551.html`,
statement clauses (1)–(7) and proof. The published statement and its
import closure are unchanged.

The implemented proof applies the published assembly theorem
`finiteTypeFiniteEtaleGenericComponentSplitting_of_fieldSplitting_and_cover`
to the proved inputs `finiteSeparableComponentSplitting` and
`finiteSeparableGenericCover`. The former is the published Stacks 054R
proof developed by Workers 1370 and 1583. The latter uses the published
prescribed-cover construction developed by Worker 105. All three are
imported by their Lean module names.

For a locally finite-type, quasi-compact morphism to an irreducible
scheme, the assembly chooses the base's generic point. The actual fibre
over its residue field is Noetherian, since it is of finite type over
a field. Thus its actual maximal irreducible components form a finite
set, and the field-splitting theorem produces one finite separable
extension over which all actual reduced components are geometrically
irreducible. The prescribed-cover theorem realizes that extension as
the residue field at the generic point of an affine irreducible finite
étale surjective cover of a nonempty open in the original base.

The assembly compares the scalar extension of the original generic
fibre with the actual generic fibre of the categorical pullback over
this cover. Its specified residue-field spectrum isomorphism and
structural triangle give an actual cartesian comparison, and the
published component transport proves the required geometric
irreducibility for every actual vanishing-ideal closed component.
Surjectivity, finiteness and étaleness of the first projection follow
by actual base change. Its target is the source of the actual open
restriction of the original morphism.

Consequently this theorem supplies the full existence conclusion of
0551 without assuming a splitting extension, a cover, or geometric
irreducibility of the components. It retains arbitrary schemes,
including nonreduced irreducible bases, and adds no Noetherianity,
separation, reducedness, flatness, perfectness or characteristic
hypothesis. The Noetherian argument concerns only the generic fibre.
Spreading geometric irreducibility beyond that fibre and generic
constancy of geometric connectedness remain separate statements.
