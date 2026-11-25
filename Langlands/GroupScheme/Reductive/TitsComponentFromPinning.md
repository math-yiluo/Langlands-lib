# Actual component witnesses directly from pinning diagrams

This derived internal assembly accepts actual factor pinning data over the exact
intermediate stabilizer field, using the original field's separable closure as
upper field. Its required diagram comparison identifies the pinning's entire
simple base with the original entire Cartan component, preserves every ordered
entry, and intertwines every full relative-Galois star permutation with restriction
to the original ground field.

The pinning-to-actual-index adapter constructs an actual Tits index of the same
extension-field group, using the fixed separable-closure comparison chosen with `IsSepClosure.equiv`.
Compose its entire vertex equivalence with the supplied component equivalence.
The two pairing formulas give all ordered Cartan entries. The two full star
identities give the precise actual-index action through the closure comparison.

When the intermediate field's pointwise fixer is exactly the original component
stabilizer, its full absolute-Galois group equivalence supplies both required
image lifts. Each lift is chosen before the universal quantifier over vertices.
The final constructor `componentFactorOfPinningComparison` assumes that the
original ambient group `G` is simply connected. It also takes a chosen actual
geometric almost-simple product presentation `D` of `G` over its separable closure,
its semisimplicity proof, and the supplied pinning/component comparison for the
selected descended factor. The exact geometric-factor stabilizer theorem supplies
the required field-fixer equality. Under these hypotheses the constructor combines
the actual index and diagram with the actual orbit Weil covering product,
including its simply connected complement, central isogeny and anisotropy.

The preceding diagram and lift lemmas apply under their stated comparison and
field-fixer hypotheses; the final group-witness assembly has the additional
simply connected ambient restriction. The input pinning/component comparison
remains an explicit premise, and its existence is not asserted here. This helper
leaves the general semisimple central-cover reduction and unconditional target
theorem to separate proofs. The final constructor retains the prescribed
field and actual descended group literally, with no characteristic restriction.
