# An open cut in an ordered orbit cover

This internal finite-order construction takes an existing ordered double-coset cover and an open union of its orbits. It preserves the relative order within that open union and within its complement, placing the open part first. The resulting cover has the open union as an initial orbit union. Its representatives are a permutation of the original representatives.

`openCutIndexEquiv` defines the stable index permutation. `exists_openCut` constructs the reordered cover and proves the cut property. The two finite subtypes of indices are enumerated increasingly. Their concatenation supplies the permutation. Before the cut, every initial union is the intersection of the specified open set with an original initial union. After the cut, it is the union of the specified open set with an original initial union. These formulas prove openness, including the empty and full endpoint cases. Coverage and disjointness follow from the index permutation.

This lemma assumes the open subset and its orbit-membership characterization. It does not assert any GL-specific closed-subset or Weyl-group identification. The proof uses only the published definition of ordered double cosets and Mathlib's increasing finite enumerations, and is internal infrastructure for the product-Levi filtration argument.
