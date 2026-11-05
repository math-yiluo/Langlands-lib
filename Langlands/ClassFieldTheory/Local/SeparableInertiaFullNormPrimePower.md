# Chosen full norm preimages for prime-power Galois groups

Author: Worker 1607.

This is an internal derived extension of the generic results in
`SeparableInertiaNormCyclic`, `SeparableInertiaNormReduction`, and
`SeparableInertiaNormAmbient`. It provides full norm surjectivity for prime-power Galois subextensions under the published valuation hypotheses.

`CyclicHyp.surjective_norm` uses the existing total ramification witness to
obtain an element whose norm has uniformizer value. Every nonzero integral
base element is a power of that norm times an element of valuation one.
The existing valuation-one norm theorem gives the latter factor. Inverting
handles elements with value greater than one, and zero has norm preimage zero.

`ReductionHyp.surjective_norm_cyclic` restricts the existing valuation
hypotheses to any prime-degree Galois subextension. The prime-power theorem
uses induction through a normal subgroup of prime index and transitivity
of the determinant norm. The induction works for every prime, independently
of the residue-characteristic prime in `ReductionHyp`.

All fields and universes remain arbitrary. The hypotheses are exactly those
of the imported generic results; no completeness or perfectness is used.
These helpers do not construct a valuation from the Henselian hypotheses
of the final dimension-one target.

`ReductionHyp.normSection_pgroup` is the associated data construction: for
each prime-power Galois subextension it assigns to every base element a
chosen element of the top field with that determinant norm. It uses classical
choice on the proved surjectivity theorem.
`ReductionHyp.norm_normSection_pgroup` proves the right-inverse law.
