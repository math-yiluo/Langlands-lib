# Order of the inertia group of complete discretely valued fields

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.InertiaRamificationCard`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite Galois extension L/K with complete discrete valuations `base` on K and `target` on L (the library's `CompleteDVF` structures), `target` extending `base`, the file computes the order of the inertia group.

`natCard_decompositionInertiaSubgroup_eq_ramificationIndex`: if the residue extension (valuation ring of L modulo its maximal ideal, over that of K) is separable, the inertia subgroup of the valuation subring of L has cardinality equal to the ramification index `ValuedExtension.ramificationIndex` of the two valuations.

The proof makes Gal(L/K) a Galois group for the extension of valuation rings, identifies the inertia group of the maximal ideal with the library's `inertiaGroup`, applies an earlier count of that group by the ramification index, and transports the result along the injective map from Gal(L/K) to the decomposition group.

Watch for: completeness and separability of the residue extension are both assumed. The subgroup measured is Mathlib's `ValuationSubring.inertiaSubgroup`, which sits inside the decomposition group, not inside Gal(L/K). The ramification index is the library's own notion for its valuation structures.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/InertiaRamificationCard.lean`: the Lean file is the source byte for byte (SHA-256 `4338776ccb53460b3357a98692cd64c9e5fd0be3d51bb961600962cdf0da2123`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
