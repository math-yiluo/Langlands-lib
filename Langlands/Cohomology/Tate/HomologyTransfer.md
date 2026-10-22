# Ordinary homological transfer on the standard resolution

Author: Worker 45.

This construction uses Mathlib's actual homogeneous standard resolution.
Applying the proved subgroup-equivariant coset coordinate map to each tuple
defines `standardCosetComparison`. Its chain-map certificate follows because
coordinatewise mapping commutes with deleting a coordinate, hence with
the alternating boundary.
The comparison also preserves the actual augmentation to the trivial
module; this certificate is proved on homogeneous generators.

The relative norm on coinvariants is applied to each coefficient-tensored
term. Its proved naturality makes it a chain map. Composing with the
comparison of standard resolutions gives `homogeneousChainTransfer`.
Mathlib's existing bar-to-standard and inhomogeneous-chain comparisons
transport this map to `ordinaryTransferChainMap` on the actual complexes
`groupHomology.inhomogeneousChains`. `ordinaryHomologyTransfer` is its
induced map on Mathlib's actual group homology. No Tate operation is used
as an input to this construction.

This is the standard resolution construction of homological transfer,
using explicit coset coordinates. Source: Serre, *Local Fields*
(Greenberg translation, GTM 67, 1979), Chapter VII section 7, printed
pages 118–119 (PDF pages 124–125), and Chapter VIII sections 1–2,
printed pages 127–130 (PDF pages 133–136). The explicit comparison with
the pinned Mathlib chain complexes is internal to this formalization.
Registered source `serre-1979-local-fields`, PDF SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

This pair constructs the ordinary map and its intrinsic chain certificate;
it makes no claim about Tate cohomology. Only finiteness of the subgroup's
coset space is needed here, and all carriers have arbitrary universe `u`.
