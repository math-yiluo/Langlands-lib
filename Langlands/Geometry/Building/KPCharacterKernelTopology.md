# Openness of the actual finite-character valuation kernel

This internal construction concerns the unchanged `characterValuationKernel`
from `KPZeroSubgroups`. Let `k` be a field with a `Valued k Γ₀` structure, and
give the rational points of an affine group scheme `G` exactly
`rationalPointTopology k G.X`, using the topology of that valued structure.
If the actual rational character module is finitely generated over the
integers, the common character valuation kernel is open.

The proof chooses a finite generating family of actual rational characters.
For a fixed rational point, character evaluation followed by the valuation on
units is an additive homomorphism from the character module to the additive
version of `Γ₀ˣ`. Its kernel is an integer submodule. If the chosen generators
have valuation one, that submodule contains their span and hence every
character. Thus the unchanged common kernel is a finite intersection of the
valuation-one conditions on the generators.

Valuation on field units is locally constant: its value at a nonzero element
is constant on a neighborhood, and the unit-value map is continuous.
Each actual character evaluation is continuous in the named canonical point
topology. Consequently each generator condition is open, and so is the finite
intersection. `characterValuationOpenSubgroup` bundles precisely the existing
subgroup, without changing its carrier.

The connected reductive corollary obtains finite generation from the published
`rationalCharacterLattice` theorem. The split-torus corollary uses the published
connected reductivity of split tori. These results require neither local
compactness nor completeness, discrete value group, or a characteristic
restriction. The topology is the valued-field topology supplied to the
construction; comparisons with other named field topologies remain separate.
The datum corollary specializes this to the actual `E.L` and
`intermediateValuation F E.L`, with the valued structure built from that
valuation, and the actual split base change of `E.T`.

The provenance is internal: the argument combines finite generation,
Mathlib's valuation neighborhood lemma, and published continuity of actual
rational-character evaluation. It establishes the kernel openness needed in
the KP norm-image route, but does not assert openness of a torus norm image or
of the actual zero subgroup.
