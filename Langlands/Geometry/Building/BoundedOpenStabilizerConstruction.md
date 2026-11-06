# Bounded open stabilizers from rank-one exchange and open generation

This internal derived unit assembles the existing exact KP bounded-open
stabilizer predicate on supplied actual parahoric-building data. It uses the
unconditional actual centralizer norm-kernel construction to remove
centralizer boundedness, the published point sharp-exchange proof to remove a
separate sharp-fixer bound, and the published Galois norm smoothness proof to
remove that whole-statement premise from centralizer-zero openness.

All results apply at every universe `u` over nonarchimedean local fields of
either characteristic. The original ambient group, represented centralizer,
root groups, normalized valuation apartment, quotient and rational-point
action are retained. Every topology is the canonical rational-point topology.
The supplied data and the remaining hypotheses are explicit; this unit does
not construct general building data or prove the unrestricted parent theorem.

`ValuationBuildingData.sharpFixerBoundedness_of_rankOneFactorization` assumes
`RelativeRoot.HasRankOneFactorization B.i`, the opposite-factor-pair input
retained by `PointSharpExchange`. Under the apartment axioms appearing in
`SharpFixerBoundednessStatement`, that published exchange theorem covers each
singleton sharp fixer by the product of its negative-root subgroup, its
positive-root subgroup and its sharp normalizer stabilizer. The existing
`sharpFixerBoundedness_of_cover` bounds this product using the now-proved
bounded image of the actual centralizer norm kernel. Thus neither a cover nor
a centralizer bound is an additional premise of the new theorem.

For actual parahoric data, `centralizerZeroCompactOpen_of_isOpen` proves the
unchanged `CentralizerZeroCompactOpenStatement` from openness alone. The
centralizer is connected reductive by the new norm-kernel construction, so
its rational-point group is a topological group. The open centralizer-zero
subgroup is closed and is contained in the compact actual norm kernel by the
published zero-subgroup norm-kernel inclusion. A closed subset of that compact
set is compact.

`centralizerZeroCompactOpen_of_productSmoothness` supplies this openness
through `isOpen_centralizerZero`, discharging its norm-smoothness input with
`GaloisNormSmoothnessProof.galoisNormSmoothness`. It retains exactly
`DerivedCoverTorusProductSmoothStatement` as a whole-statement hypothesis.
It does not prove that remaining product-smoothness statement.

`hasBoundedOpenStabilizers_of_rankOne_and_isOpen` applies the exact
`BoundedOpenStabilizerAssembly` to the newly derived sharp-fixer bound and
unconditional centralizer bound. Its remaining inputs are the full apartment
predicate, opposite factor pairs, the whole
`OpenRootCentralizerGenerationStatement`, and openness of the actual
centralizer-zero subgroup. The existing assembly uses the exact product
formula for original apartment-point norm-one fixers and conjugation to
transport boundedness and openness to every point of the original quotient.

`hasBoundedOpenStabilizers_of_rankOne_and_productSmoothness` replaces the last
openness input with `DerivedCoverTorusProductSmoothStatement`, using the
proved Galois norm smoothness as above.
`boundedOpenStabilizerDataOfRankOne` bundles each unchanged norm-one
stabilizer as an open subgroup with equality of underlying subgroups and
algebraic boundedness.

The provenance is this composition of named published or separately staged
actual-object results; no new independent literature assertion is used.
Apartment axioms including AS 5, opposite factor pairs, open root-centralizer
generation and derived-cover/torus product smoothness remain proof
obligations, as does existence of the supplied data for arbitrary connected
reductive groups. The compact-open centralizer-zero conclusion in the second
variant remains conditional on product smoothness.
