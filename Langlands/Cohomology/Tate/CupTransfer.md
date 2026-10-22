# Cup products and subgroup maps

Proof author: Worker 45. Audit and documentation preparation: Worker 211.

The degree-zero second-factor laws follow from the proved formula expressing
multiplication by an invariant vector as the actual coefficient map. Coefficient
naturality of the constructed restriction and corestriction then proves the
restriction identity and projection formula in every first degree.

The module also supplies the connecting-map formulas with explicit successor
degrees, tensor exactness after restriction, and the actual restricted tensor
augmentation isomorphism. The latter follows by identifying the tensor with a
coinduced representation and using its proved acyclicity after restriction.
These certificates extend both formulas to all second degrees. Positive-degree
induction lifts the second class through the embedding sequence and applies
the actual boundary laws. Negative-degree induction applies the injective
tensor augmentation boundary. The sign `(-1)^p` cancels because its square is
one. Restriction uses the proved acyclicity after subgroup restriction;
corestriction uses the original tensor acyclicity.

The final results `tensorCup_restriction` and `tensorCup_corestriction` hold for
all integer bidegrees. The latter states
`Cor(a cup Res(b)) = Cor(a) cup b`. Applying the equivariant map induced by a
coefficient pairing gives `cup_restriction` and `cup_corestriction`.
No flatness condition is needed: the sequences used for this induction have
proved scalar splittings.

The conventions are those of Serre, *Local Fields* (1979), VII §7 and VIII §§1–3,
printed pages 118–119 and 127–132; source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Serre refers to Cartan–Eilenberg for formulas involving restriction and
corestriction without displaying these two formulas. The precise identities
here are derived internally by the coefficient naturality and dimension-shift
argument above.

The module uses the actual Mathlib Tate objects, the constructed
`restriction` and `corestriction`, and the dimension-shifted `tensorCup`.
