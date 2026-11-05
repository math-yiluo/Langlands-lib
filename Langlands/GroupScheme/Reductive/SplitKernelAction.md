# Actions on split kernels with wound scalar-extension quotient

Author: Worker 1608.

This internal auxiliary construction induces an actual automorphic action
on a supplied smooth affine split closed kernel. It assumes an actual fppf
quotient and an extension field over which that quotient has only constant
affine-line maps and the product of the acting group with the kernel has
dense actual rational points. The acting group is smooth. The quotient is
separated. No connectedness, perfectness, characteristic or algebraicity
condition is imposed on the field extension.

The proof first treats the case where the woundness and density are over
the ground field. Each rational point of the acting group gives an actual
automorphism of the ambient group. Its composite from the split kernel
to the wound quotient vanishes by the published finite split-series
rigidity theorem. Density and reducedness of the smooth product give
vanishing of the universal action morphism followed by the quotient.
The full all-relative-test kernel equality then gives stability on all
test schemes.

For a field extension the same proof applies to the actual pulled-back
objects, quotient and action. Splitness is preserved by the published
split-series base-change theorem. Stability descends through the fpqc
map of spectra: pull back a test scheme and its two points, apply
extended stability, and descend the factorization through the representing
monomorphism using effective epimorphism descent. This step imposes no
lifting or section assumption on the original quotient or field map.

`onSplitKernelOfWoundBaseChange` is actual action data, constructed by
factoring through the represented stable subgroup. Its accompanying
equivariance theorem identifies the new action with the original one
after the inclusion on every test.

The provenance is internal: this composes the existing actual-action,
split-source rigidity, rational-density morphism detection, split-series
base change and fpqc descent APIs. It implements the geometric stability
step used in the ambient split-radical argument. It does not prove
separable invariance of woundness, density over separably closed fields,
the central additive-subgroup criterion, or the unchanged
`SplitRadicalWoundQuotientStatement`.
