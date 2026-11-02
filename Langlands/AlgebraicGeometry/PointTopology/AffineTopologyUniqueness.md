# Uniqueness of the affine evaluation topology

Author: Worker 105.

The target is `AffineTopologyUniquenessProperty` in `AffineTopologyAxioms`.
It is the coordinate-algebra intermediate uniqueness assertion described there,
derived from Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Proposition 2.1, printed page 2. Registered source
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

`affineTopologyUniqueness_proof` extracts functoriality, binary pushout
compatibility, quotient embeddings and line normalization from the
hypothesis and applies `affineTopology_eq_evaluation_of_pushouts`. Its
implemented proof is described in the paired Markdown of
`AffineTopologyBinaryUniqueness`: equivalence transport and finite
empty/option induction identify finite polynomial point topologies,
then a finite polynomial presentation and the quotient embedding property
identify each finite-type algebra's topology.

No finite coproduct axiom is assumed. Only the value ring has a topology,
with continuous ring operations. No Hausdorffness, locality or finite
presentation is imposed. The base and coordinate algebras have a common
universe, while the value ring may have a different universe.

This proves uniqueness under the intermediate coordinate-algebra axioms.
The bridges to actual affine scheme topology assignments and existence
for the full axiom package remain separate obligations. This file does
not claim the full scheme assertion of Proposition 2.1 or whole-paper
completion.
