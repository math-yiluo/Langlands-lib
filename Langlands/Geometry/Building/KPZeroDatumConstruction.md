# Actual zero-subgroup data from simply connected derived covers

This internal construction fills the torus and embedded splitting-field
choices required by `UnramifiedZeroDatum`, starting from actual supplied
simply connected derived-cover maps. It then assembles `ZeroSubgroupDatum`
at a prescribed maximal split torus and centralizer, and extends supplied
`ValuationBuildingData` to `ParahoricBuildingData`.

The arbitrary universe `u`, both characteristics, and the existing
`UnramifiedClosure F` and `SeparableClosure F` are retained. Cover existence
is an explicit dependency. This module does not prove the unconditional
root-valuation building construction.

The generic supporting theorem `exists_isMaximallySplitMaximalTorus`
chooses a maximal split torus and extends it to a maximal torus in an affine
group locally of finite type. `exists_finiteGaloisSplittingField_inside`
uses the published finite Galois splitting theorem, embeds its splitting
field into the specified separably closed field, and transports its finite
dimension, Galois property and splitting isomorphism to the embedding's
image. These are derived constructions from existing Library theorems.

`UnramifiedZeroDatum.ofDerivedCover` applies these two results to the group
over the actual inertia field. The supplied cover guarantees connected
reductivity and hence the affineness and finite type needed for torus
existence. Its maximal torus is affine as a closed subgroup of an affine
group. The finite Galois splitting field is an actual intermediate field
of `SeparableClosure F` over `UnramifiedClosure F`. The cover's source,
target, derived inclusion and covering morphism become the corresponding
fields of the output.

`ZeroSubgroupDatum.ofDerivedCovers` retains the given maximal split torus
and all-test centralizer representative. It constructs the centralizer's
unramified zero datum from a supplied cover of that base-changed
centralizer and retains a second supplied cover of the ambient group.
`ParahoricBuildingData.ofDerivedCovers` applies this to the exact torus and
centralizer of its supplied `ValuationBuildingData`. Its underlying
valuation building data is definitionally the input, preserving the
apartment, root filtrations, quotient, and rational-point action.

The source context is KP Definition 2.6.2 (printed p.93, PDF124),
Definition 2.5.13 (printed p.90, PDF121), and Definitions 2.6.20 and
2.6.23 (printed p.104, PDF135). This is an internal assembly of the
existing Library definitions, rather than a claim that KP states these
constructors verbatim. The 2024 corrections, PDF25, retain the henselian
perfect-residue-field hypotheses for Definition 2.6.20 and subsequent
definitions; the local-field setting here meets those hypotheses.

No existence theorem for simply connected derived covers, no independence
of zero-subgroup choices, no quasi-split reduction, no actual apartment
existence, no descent, and none of the five building axiom witnesses is
proved here. The constructors use no restriction on rank, residue size,
ramification, or characteristic.
