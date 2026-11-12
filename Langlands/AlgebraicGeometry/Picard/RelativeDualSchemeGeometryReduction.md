# Residue-field comparison and reduction of relative dual geometry

This is an internal construction and two conditional lemmas supporting
`Langlands.AbelianScheme.RelativeDualSchemeGeometryStatement`. It uses the
published universal-base-change proof and retains the four still-required
geometric inputs explicitly. It does not prove the relative geometry statement
without those inputs.

The fibre argument and final reduction develop the carried Task 892 draft,
originally designed by Worker 301. Worker 892 introduces the named
residue-field comparison and discharges the draft's former
`PicardZeroUniversalBaseChangeStatement` premise using the published theorem
`picardZeroUniversalBaseChange`.

## The actual residue-field comparison

For every scheme `S : Scheme.{u}`, abelian scheme `A` over `S`, proof
`hA : HasDualScheme A`, and point `s : S`,
`Langlands.AbelianScheme.dualSchemeResidueFieldIso A hA s` is an isomorphism
in `Over (Spec κ(s))`. Its source is the pullback of the actual chosen
`dualScheme A hA` along `S.fromSpecResidueField s`. Its target is the
chosen dual of the abelian scheme obtained by the same base change.
The target's representability proof is
`hasDualScheme_baseChange picardZeroUniversalBaseChange
  (S.fromSpecResidueField s) A hA`.

The construction specializes the published `dualSchemeBaseChangeIso`.
That comparison uses universality of the actual base-changed Poincare
family and uniqueness of a universal family. The theorem
`picardZeroUniversalBaseChange` supplies this universality, including
classification on every test scheme and compatibility with actual
rigidified pullbacks. No new comparison of only geometric point sets is
used here. The source's structural morphism is definitionally
`(dualScheme A hA).hom.fiberToSpecResidueField s`.

## Geometry of the fibres

`dualScheme_fiberToSpecResidueField` assumes
`field : FieldDualSchemeGeometryStatement.{u}`. For arbitrary `S`, `A`,
`hA`, and `s` as above, it proves that this fibre morphism is smooth and
geometrically connected. No quasi-separatedness assumption is needed
for this lemma or the comparison isomorphism.

Apply `field` to the abelian scheme over `Spec κ(s)` and its
representability proof supplied by base change. The triangle equation
`Over.w` for `dualSchemeResidueFieldIso` expresses the original fibre
morphism as the comparison isomorphism followed by the structural
morphism of that field dual. Smoothness and geometric connectedness
respect isomorphisms, as follows from their stability under base change.
`MorphismProperty.cancel_left_of_respectsIso` transfers the two field
properties to the original fibre morphism. The properness component of
`field` is unused.

## The relative reduction

`RelativeDualSchemeGeometryStatement.of_flat_finitePresentation_proper`
takes proofs of exactly four published proposition definitions:

- `FieldDualSchemeGeometryStatement.{u}`;
- `RelativeDualSchemeFlatStatement.{u}`;
- `RelativeDualSchemeFinitePresentationStatement.{u}`;
- `RelativeDualSchemeProperStatement.{u}`.

It returns `RelativeDualSchemeGeometryStatement.{u}`. Fix a
quasi-separated base `S`, an abelian scheme `A` over it, and
`hA : HasDualScheme A`. The flatness and finite-presentation inputs
supply the hypotheses of Mathlib's
`Smooth.of_smooth_fiberToSpecResidueField`; the first part of the fibre
lemma supplies smoothness of every residue-field fibre. This proves
smoothness of the structural morphism of `dualScheme A hA`.
Properness is supplied directly by the properness input. The second
part of the fibre lemma and
`GeometricallyConnected.iff_geometricallyConnected_fiber` prove
geometric connectedness of that same morphism.

The only relative inputs beyond field geometry are flatness, local
finite presentation, and properness. This module neither discharges
them nor establishes dual existence. In particular, fibre geometry
alone does not supply flatness or properness.

## Provenance and source scope

The comparison is a specialization of accepted Library constructions;
the subsequent arguments use Mathlib's results about scheme morphisms.
This internal derivation does not invoke a new literature theorem.
The mathematical scope of the final target remains Lan's
Theorem 1.3.2.3, as documented in
`RelativeDualSchemeGeometryStatement.md`: arbitrary quasi-separated
bases, without a noetherian, reducedness or projectivity assumption.
That source scope does not discharge any of the four proposition
inputs above. The exact target, `HasDualScheme`, `dualScheme`, and their
dependency closure are unchanged.
