# Original curve-place local coordinates of a space Weil restriction

This internal arithmetic specialization gives field and integral tensor
Weil point homeomorphisms over principal curve S-integers. It allows
arbitrary finite extensions, including inseparable ones.

Let `k` be a finite field, `K` a global function field over `k`, and `L/K`
a finite extension with the specified compatible `k`-algebra structures.
Choose `s : K` with `K` finite-dimensional over `k(s)` and a nonzero `t`
in the corresponding curve chart ring. The lower coefficient ring is the
ring of S-integers for `curvePlacePrincipalExceptional k K s t`; the upper
one uses the full preimage of that exceptional set in `L`.

For a quasi-separated finite-type space `X` over the upper ring, assume
that its Weil restriction to the lower ring is algebraic.
`fieldPointHomeomorph` identifies that Weil space's points over the original
completion at `v` with the product of `X`'s points over all original upper
completions above `v`. Each topology is the original field-valued topology.
The proof uses the published principal S-integer field tensor equivalence,
continuous scalar multiplication from the actual completion embeddings,
the module topology from completeness and finite dimension, and the
published henselianity of each independently normalized completion norm.

Outside the principal exceptional set, `integralPointHomeomorph` gives the
same comparison over the completed valuation rings. Their point topologies
are induced through the original inclusions into the completed fields.
The proof applies the integral tensor comparison using the original
completed-integer and field tensor equivalences. The compatibility square
of the original coefficient inclusions is definitional.

The component formulas identify both maps exactly with
`completedTensorSpaceWeilRestrictionPointMap` for the specified arithmetic
tensor equivalences. `isHomeomorph_fieldPointMap` gives the field property
in the form used by the integral construction.

The provenance is internal application of arithmetic tensor, local field,
and tensor point topology results. No separability, scheme, projectivity,
or smoothness hypothesis on `X` is introduced. Original Weil algebraicity
remains a premise; the adelic stages and endpoint are not proved here.
