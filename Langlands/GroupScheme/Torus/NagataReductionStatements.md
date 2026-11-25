# The three independent implications in Nagata's theorem

`IsLinearlyReductive G` is exactly the existing all-test condition that every
finite-coordinate matrix representation is the sum of its simple stable
subspaces. It is an abbreviation of mathematical content already present in
`NagataLinearlyReductiveStatement`; no new representation convention is imposed.

This module gives three Prop-valued statement definitions, each in every universe
and with exactly the finite-type affine field-group and nonzero-characteristic
hypotheses of the published target:

- `NagataIdentityComponentNecessityStatement`: linear reductivity implies that
  there exists an actual open group-scheme inclusion onto the identity set whose
  source is of multiplicative type.
- `NagataComponentOrderNecessityStatement`: linear reductivity implies that the
  characteristic does not divide the `Nat.card` of the geometric components.
- `NagataLinearlyReductiveSufficiencyStatement`: these two geometric conditions
  together imply linear reductivity.

The actual identity-set immersion, multiplicative-type predicate and geometric
component type are precisely those in the original target. None of these three
statements is proved in this module. In particular the first statement retains
arbitrary imperfect fields, non-smooth groups and all finite-dimensional
representations; it is not a smooth or commutative substitute.

The only proofs are the elementary logical assembly
`nagataLinearlyReductive_of_parts` and equivalence
`nagataLinearlyReductive_iff_parts`. They distribute the implication into the
conjunction in the unchanged published target and recombine those implications.
They supply no proof of any structural condition.

## Provenance

Milne, *Algebraic Groups* (2022 corrected reprint), Definition 12.52, printed
p.248 (PDF p.259), defines linear reductivity by semisimplicity of every
finite-dimensional representation. Remark 12.56, printed p.249 (PDF p.260),
states exactly the characteristic-positive equivalence split here. The original
passages were read in the retained registered source
`milne-2022-algebraic-groups`, SHA-256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`.
The source-to-Lean correspondence is the same as that of the unchanged
`NagataLinearlyReductiveStatement` pair, imported by this module.

The registered official errata snapshot
`milne-2022-algebraic-groups-errata-2026-11-04` was read in full; it has no
correction to Definition 12.52 or Remark 12.56. The 2017 edition's incorrect
"torus" wording is not used. Milne refers to Demazure–Gabriel IV, section 3,
Theorem 3.6 for the general non-smooth proof, which remains unavailable; this
module states propositions and does not rely on having that proof.

These three statements are derived by separating the two necessary conclusions
and the sufficient implication of the published theorem. This decomposition
separates substantial prerequisites without changing or weakening
`NagataLinearlyReductiveStatement`.
