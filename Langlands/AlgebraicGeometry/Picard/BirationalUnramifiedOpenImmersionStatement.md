# Birational unramified morphisms over geometrically unibranch bases

`Langlands.AlgebraicGeometry.BirationalUnramifiedOpenImmersionStatement`
asserts that a separated, locally of finite type, formally unramified morphism
`f : Z ⟶ S` between integral schemes is an open immersion when `S` is
geometrically unibranch and `Scheme.BirationalOver f (𝟙 S)` holds. The
proposition is universe-polymorphic and has no outer hypotheses. This module
defines the proposition; it does not prove it.

The birationality hypothesis uses Mathlib's actual dense open subschemes and
an isomorphism between them compatible with the displayed maps to `S`.
Since both schemes are integral, this supplies dominance and an isomorphism
on their generic stalks, hence the birationality used in the cited EGA
results. `GeometricallyUnibranchIntegralScheme S` is the published condition
on the actual local domains of `S`, their normalization in their fraction
fields, and the induced residue-field maps.

This is a derived integral-scheme consequence of Grothendieck and Dieudonne,
*EGA IV*, fourth part (1967), Remark 18.10.2(iii), printed pp.158–159, and
Lemma 18.10.18, printed pp.166–167. The registered source is
`grothendieck-dieudonne-ega-iv4-1967`, SHA256
`b4277fb99c6edf8feec5b01f54368e4b8521bcd52871316c0edf6ff4ae69389e`.
No source-specific project errata file was found. The original List 3 has
no identified correction to these two assertions.

For the derivation, dominance between integral schemes gives injectivity of
the induced local-ring maps. Remark 18.10.2(iii) then gives étaleness: the
base is locally integral, and the morphism is locally of finite type and
formally unramified. Lemma 18.10.18 gives the open immersion from étaleness,
separatedness and birationality. The use of the locally integral clause in
18.10.2(iii) retains local finite type without adding finite presentation.

This proposition is the general morphism prerequisite in the closure route
to `UnramifiedGenericSectionExtensionStatement`. Its hypotheses do not
include closedness of irreducible images or a section. Applying it to an
integral closure of a section image, and establishing surjectivity and the
prescribed generic restriction, are separate obligations. Neither scheme
is assumed noetherian or quasi-compact, and the base need not be normal.
