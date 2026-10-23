# The global degree denominator of the total idele invariant

For a Galois extension `E/F` of number fields in an arbitrary common universe,
`totalIdeleInvariantToDenominator` restricts the codomain of
`totalIdeleInvariant` to `denominatorSubgroup (Module.finrank F E)`. The supplied
local invariant family and its `RelativeImages` hypothesis are unchanged, as
are the explicit choices of finite and infinite places.

The denominator bound follows internally from existing group cohomology.
The published ordinary restriction-corestriction identity multiplies a
degree-two class by the subgroup index. Apply it to the trivial subgroup:
positive-degree cohomology of that subgroup is zero, so corestriction is the
zero map. The index is the cardinality of the finite group. Hence that
cardinality annihilates every degree-two class.

For the actual idele representation, the Galois group cardinality equals
`Module.finrank F E`. Applying the additive total invariant to this
annihilation identity puts its value in the denominator subgroup, which is
defined by precisely that annihilation condition. Codomain restriction then
defines the new map, and its coercion recovers the original total invariant.

Finally, the existing conditional kernel-vanishing theorem remains true for
the restricted map by injectivity of the subgroup inclusion. This last lemma
still explicitly assumes reciprocity for every field-unit cohomology class.
The module does not prove reciprocity, surjectivity of the total invariant,
or the existence of the global invariant family. Its provenance is the
internal combination of `IdeleTotalInvariant`, `OrdinaryTransferLawsProof`,
Mathlib's positive-degree vanishing for the trivial group, and the Galois
group cardinality formula.
