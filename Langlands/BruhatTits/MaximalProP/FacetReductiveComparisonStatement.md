# Facets and the reductive quotients of supplied KP models

This is a derived prerequisite statement for corrected Kaletha–Prasad
Proposition 13.5.2. It is not a proof of that proposition or of the comparisons
stated here.

`FacetReductiveComparisons D` concerns the actual building facets and the
specified integral models and special-fibre quotients of `D`. It asserts three
comparisons.

1. The connected reductive quotient at a facet `Fa` is a torus exactly when
   `Fa` is a chamber.
2. If `Fa` is a face of `Fb`, the actual schematic image of the neutral
   special-fibre model morphism in the reductive quotient at `Fa` is a
   geometric Borel subgroup exactly when `Fb` is a chamber. The predicate is
   `IsGeometricBorelSubgroup`: the inclusion is Borel over the residue field
   and remains Borel over its algebraic closure.
3. For the same incident pair, let `P` be that schematic image and let
   `j : U ⟶ P` be any represented unipotent radical. Pull back the range of
   `U(𝓀[F]) → P(𝓀[F]) → Gred_Fa(𝓀[F])` through `Q.parahoricReduction`,
   where `Q` is the quotient datum at `Fa`. Its image under the inclusion of
   the neutral integral-point subgroup into `G(F)` equals the supplied
   positive subgroup at `Fb`.

In particular, the third equality is an equality of subgroups of the original
`G(F)`, not merely of integral sections or residue-field points. It uses the
range of the radical's rational-point map, without identifying all rational
points of a schematic image with the image of rational points. The assertion
holds for all incident pairs, including equality, rather than only for
incident chambers.

`FacetReductiveComparisonStatement.{u}` quantifies over an arbitrary universe,
a nonarchimedean local field `F`, an affine group scheme `G` over `F`, and a
supplied `KPBuildingDatum G`. Its sole additional premise is
`D.SatisfiesGroupAxioms`. Connected reductivity and the building, integral
model and quotient data are already part of this datum. This premise is
provided by availability in the host proposition; global `IsValid` is not
required. No extra maximal-subgroup or normalizer conclusion is included.

The statement is derived from the following original-source ingredients in
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023).

- Axiom 4.1.22 and Remark 4.1.23, printed pp.163–165 / PDF pp.194–196,
  relate incident facets to parabolic images, their reduction preimages,
  root data and positive radicals, and characterize chambers by the absence
  of proper residue-field parabolics.
- Theorem 8.4.10 and Corollary 8.4.12, printed pp.305–306 /
  PDF pp.336–337, give the root-datum and positive-radical comparisons for
  the constructed models over the maximal unramified extension.
- The proof of Proposition 13.5.2, printed pp.476–477 / PDF pp.507–508,
  uses incident chambers as Borel subgroups, chamber reductive quotients as
  tori, and the corresponding radical preimages.

The exact universally quantified statement about supplied data is not quoted
verbatim from the book. Its proof must derive the comparisons from the
single-group axioms and use the finite residue field, in particular the
quasi-splitness of connected reductive groups over finite fields. The chapter
8 construction alone does not assert descent for arbitrary supplied models.
The order-bijection clause in the current Library records a bijection with
one-way reversal of incidence; it must not be silently treated as an order
isomorphism. The radical-preimage equality also requires a comparison through
the represented quotients, beyond the positive-subgroup monotonicity clause.

The 1 November 2024 *Corrections and additions*, PDF p.49, changes the
ambient group in Proposition 13.5.2(1) to `G(F)^0`. The comparisons here use
actual facet model subgroups and do not assert an ambient maximality claim.
They do not concern an independently supplied Moy–Prasad filtration.
