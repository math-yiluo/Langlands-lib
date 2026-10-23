# Bounded automorphisms on rational domains and sections

Author: Worker 36.

This derived construction uses the automorphism group of an actual presented
strict affinoid algebra in its category of bounded algebra maps. It constructs
left actions on chosen rational presentations, spectrum points and the total
space of actual quotient-algebra sections. Group multiplication is function
composition: the right factor acts first. Rational input elements move by the
forward algebra map; spectrum points move by the inverse algebra map. Each
individual spectrum operator is continuous. No topology on the automorphism
group or joint continuity is assumed or asserted.

The exact image formula for a moved rational locus follows from the two inverse
maps. Arbitrary point-covering families are preserved and reflected. The induced
functors on the rational inclusion category obey the identity and multiplication
laws and are continuous for the finite rational topology. The published natural
presheaf isomorphism supplies `presheafIso` for each operator.

`TotalSections P` consists of a chosen rational presentation and an element of
its constructed quotient algebra. `sectionMap` uses the actual bounded
comparison map. Its identity and multiplication laws follow from uniqueness of
bounded maps out of a rational quotient and the equations on the base map.
These laws give a genuine group action on total sections. The last theorem
proves that this transport commutes with bounded restriction maps.

The geometric provenance is Berkovich, *Non-archimedean analytic spaces*, Trieste
lectures (2009), Definition 2.1.11, p. 8, and Definition 2.2.1 and Exercise
2.2.2(ii), p. 9: bounded maps act contravariantly on affinoid spectra, and rational
domains are represented by their quotient algebras. Registered source
`berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
The group actions and their coherence are derived from the Library's actual
pullback, comparison, uniqueness and bounded-equivalence constructions, not
separately numbered claims of that source.

Rational radii remain one and the base is a presented strict affinoid algebra.
The section construction requires a complete ultrametric normed scalar field.
It permits zero and nonreduced quotient algebras and trivial valuations. It
constructs no general analytic atlas, continuous topological-group action,
sheaf descent, etale site or equivariant etale site.
