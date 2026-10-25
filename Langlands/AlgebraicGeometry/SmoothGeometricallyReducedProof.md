# Proof that smooth morphisms are geometrically reduced

Worker 129 authored the Lean helper and exact-target wrapper. Worker 428
checked the implementation and prepared the proof submission and documentation.

`Langlands.AlgebraicGeometry.smoothGeometricallyReduced.{u}` proves the
published proposition
`Langlands.AlgebraicGeometry.SmoothGeometricallyReduced.{u}` without changing
its statement pair or imports. It introduces arbitrary schemes `X` and `S`,
a morphism `p : X ⟶ S` and its smoothness hypothesis, then applies
`SmoothReducedProof.geometricallyReduced_of_smooth`.

The helper applies smoothness under base change to reduce geometric
reducedness to reducedness of schemes smooth over fields. Affine charts
reduce this to smooth algebras. A smooth algebra over a domain has standard
etale polynomial charts; these are reduced by injection into their
fraction-field base change. Testing nilpotents in every maximal localization
then proves reducedness. [SmoothReducedProof.md](SmoothReducedProof.md)
describes the implemented steps and their provenance from the reducedness
part of Stacks Project Tag 056T, Lemma 33.25.4, in registered source
`stacks-global-functions-field-and-fibre-criterion-2026-10-23` (directory
SHA256 `c170b7f07df230ebbd77e6b3dc8774e0061520328c065c87cfd45554d2ddb850`).

The exact proposition covers arbitrary base schemes and arbitrary universes.
There are no properness, noetherian, characteristic, connectedness or
nonemptiness assumptions. This focused helper proof supports the subsequent
field global-functions proof.
