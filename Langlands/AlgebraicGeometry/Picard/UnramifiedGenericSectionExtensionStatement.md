# Extension of generic sections of unramified morphisms

`Langlands.AlgebraicGeometry.UnramifiedGenericSectionExtensionStatement`
asserts the following. Let `S` be an integral scheme, geometrically
unibranch at every point, and let `p : X ⟶ S` be separated, locally of
finite type, and formally unramified. Suppose that every closed
irreducible subset of `X` has closed image in `S`. Every actual map
`Spec κ(η) ⟶ X` over the canonical generic residue-field map
`Spec κ(η) ⟶ S` then extends to an actual section `S ⟶ X` of `p`,
and the restriction of that section is the specified generic map.
The proposition is expressed as surjectivity of
`genericSectionRestriction p`, so the equations over `S` and the
restriction equality are part of its conclusion.

This is a derived integral-base specialization of the final assertion
of Grothendieck and Dieudonne, *EGA IV*, fourth part (1967),
Proposition 18.10.19, printed p.167. The registered original is
`grothendieck-dieudonne-ega-iv4-1967`, SHA256
`b4277fb99c6edf8feec5b01f54368e4b8521bcd52871316c0edf6ff4ae69389e`.
The original List3 errata was checked, with no correction to this
proposition found; no source-specific project errata note was found.

EGA assumes a reduced base with locally finitely many irreducible
components and begins with a rational section. Integrality supplies
reducedness and exactly one irreducible component, and hence the
local finiteness condition. Local finite type supplies spreading of
the given generic map to a rational section. In the present
formalization, Mathlib supplies
`Scheme.RationalMap.equivFunctionField`; the canonical residue map
at the generic point identifies its function-field spectrum with the
generic residue-field spectrum. This is the construction implemented
in the separate `genericRationalSectionEquiv` adapter. EGA's conclusion
that the rational section is defined at every geometrically unibranch
point then gives a section on all of `S` with the prescribed
restriction. This module states that existence conclusion; it does
not prove EGA's extension argument.

The condition `GeometricallyUnibranchIntegralScheme S` uses the
actual stalks and their canonical normalization and residue-field
maps, specialized to domains. `ClosedIrreducibleImages p` is a
condition on the displayed map on the displayed base. There is no
noetherianity, dimension, or rank assumption and no closed-image
condition after arbitrary base changes. Formal unramifiedness and
local finite type are both explicit hypotheses. The assertion is
universe-polymorphic.

Two small internal consequences connect the base hypothesis to
valuation spectra. The proved theorem
`geometricallyUnibranchIntegralScheme_of_hasNormalStalks` takes the
integral-closedness component of each actual normal stalk and applies
`geometricallyUnibranchIntegralScheme_of_stalks`.
`valuation_spec_geometricallyUnibranch` applies this implication to
`valuation_spec_hasNormalStalks`. It therefore includes valuation
domains of arbitrary rank and fields. These lemmas prove only the
base property, not the section-existence proposition.

The separate `genericSectionRestriction_injective` gives uniqueness
under the separatedness hypothesis. The new proposition isolates
the missing existence step. Its proof alone would not establish a
correspondence representer, its hypotheses in a bundle problem, or
the actual line-bundle extension required by
`ValuationRingTwoAxisExtensionStatement`.
