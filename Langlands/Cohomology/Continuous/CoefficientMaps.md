# Coefficient maps on the finite quotient system

Author: Worker 22. The imported comparison definition and its prerequisites
are published in Library commit `1058c134c0d2fb45ec96d08ea2956983aaac1d80`.

`finiteCochainCoefficient f` maps the actual finite quotient cochain
diagrams for representations `A` and `B`, where `f : A ⟶ B`.
Its component at `N` is the ordinary cochain map for the identity
homomorphism of `G / N` and the fixed-coefficient morphism supplied by
`Rep.quotientToInvariantsFunctor`. Naturality with respect to inflation
is proved using the ordinary cochain composition formula: both group
maps agree and both coefficient maps apply the same underlying `f`.

`finiteCohomologyCoefficient f q` applies the homology functor in natural
degree `q` to this natural transformation. The selected
`finiteQuotientCoefficient f q` is its actual colimit map.
Identity and composition laws are proved on cochains, then transported
through the homology and colimit functors. These are the structural
certificates for coefficient functoriality.

`continuousCoefficientCochains f` uses Mathlib's continuous cochain map
for the identity group homomorphism and the supplied morphism between
discrete topological representations, with topology forgotten. Its
compatibility with finite-stage and colimit comparisons is asserted and
proved in the separate coefficient comparison statement and proof pairs.

The coefficient ring, group, and coefficient carriers retain arbitrary
common universe `u`. No finiteness or compactness assumption is used in
the definitions or structural laws. Under compactness the ordinary
quotient stages are finite.

These constructions are derived from Serre, *Local Fields* (1979),
VII §5, printed pp.115–117 / PDF pp.121–123, and X §3, printed p.154 /
PDF p.160. The former gives compatible coefficient and group maps; the
latter supplies the inflation-indexed limit to which the implemented
coefficient functoriality applies. The Lean implementation uses the actual
Mathlib maps and colimit.

Literature ID `serre-1979-local-fields`; SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`;
retained file `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
Environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
