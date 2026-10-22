# Relative residue maps of actual p-adic field embeddings

Author: Worker 53. This is a definition and construction contribution.

For every prime and every two `PadicField` objects in independent universes,
an actual algebra homomorphism over the specified `Padic p` base induces
`extensionIntegerMap` and `extensionResidueMap`. Both use the canonical
topological realizations and their actual valuation integer rings and residue
fields. No valuation-preservation certificate or residue embedding is an
additional input.

The spectral norm is defined from the minimal polynomial over the p-adic base.
An injective algebra homomorphism preserves that polynomial. The lemma
`canonicalNorm_map` therefore proves preservation of the base-extending norm.
This implies preservation of the unit ball and of the strict unit ball.
The first fact constructs the integer-ring homomorphism; the second proves it
is a local homomorphism. Mathlib's residue-field functor then constructs the
residue map, whose representative formula is proved directly.
`extensionResidueAlgebra` installs the precise scalar structure induced by
this map, and `extensionResidueDegree` is its relative vector-space dimension.

`extension_isometry` exposes the preserved metric for the two selected
canonical normed-field structures. Both the integer and residue maps respect
identity embeddings and composition in three independent field universes.
The residue identity and composition proofs evaluate on actual quotient
representatives, using surjectivity of reduction.

The residue extension is finite because both actual residue fields are finite.
`extensionResidueDegree_pos` makes its strictly positive degree available.
`extensionResidueCardinality` proves
`q_E = q_F ^ extensionResidueDegree F E f` by Mathlib's finite-dimensional
vector-space cardinality theorem. Identity embeddings have residue degree
one; degrees multiply in towers. The tower proof installs the three precise
residue scalar structures, derives their scalar-tower compatibility from
composition of the actual residue maps, and applies multiplicativity of
`Module.finrank`. `extensionResidueCardinalityUnit` transports the same
formula to the complex units used by norm characters.

These are derived instances of the valuation and residue-extension mechanisms
in Serre, *Local Fields*, English translation (1979), Chapter II, section 2,
Proposition 3 and Corollaries 1–3, printed pages 28–29, PDF pages 36–37.
The original pages 28–30 / PDF 36–38 were read directly in
`C:/Central-Library/Serre--Local Fields--1979.pdf`.
Registered source: `serre-1979-local-fields`, SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The implementation proves norm preservation by the minimal-polynomial
description already used by the project's canonical construction; it does
not reprove the general uniqueness theorem or the ramification-degree formula.

The cardinality and relative-degree formulas are derived finite-field linear
algebra applied to these constructed residue embeddings. No formula for
normalized field norms or an equality between field degree and ramification
index times residue degree is claimed in this pair.

The project imports are `Langlands.LocalField.CanonicalProof` and
`Langlands.Weil.Local.ResidueCharacters`, published and current at Library
`30ceb5a0d89d8094c1663fc19f35416519b9a125`. The latter supplies the actual
integer and residue definitions through
`Langlands.LocalField.Normalization.Definitions`. Pinned Mathlib supplies `minpoly.algHom_eq`,
the spectral norm, the local-hom criterion, and
`IsLocalRing.ResidueField.map`, as well as `Module.card_eq_pow_finrank`,
`Module.finrank_pos`, and `Module.finrank_mul_finrank`.
The environment is Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
All new maps and their intrinsic obligations
are authored here; the imported theories retain their original authorship.

This module constructs maps on the actual finite residue fields, not maps on
their algebraic closures. Compatibility of chosen closure comparisons with
absolute residue actions, the actual local Weil-group inclusion, finite index,
openness, inertia intersection and degree/norm scaling remain additional
obligations. They are not silently assumed in these constructors.

Native compilation of this complete pair succeeds without warnings or errors
against the published dependencies. This is development verification;
independent semantic review and Library publication remain required.
