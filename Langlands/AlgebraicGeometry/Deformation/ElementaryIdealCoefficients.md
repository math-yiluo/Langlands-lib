# Constant coefficients of an elementary ideal on flat affine tests

Let `I` be an ideal annihilated by the maximal ideal `m` of a local ring `R`.
For a flat `R`-algebra `C` the ideal `IC` is annihilated by `mC` and receives
its action from the fibre ring `C/mC`. Flatness identifies `IC` with the tensor
product of `C/mC` over `R/m` with `I`. This is the scalar and ideal comparison
in SGA 3, Exposé III, §0, specialized to affine tests. The Lean comparison uses
`ElementaryKernelTensor.idealTensorEquiv` and its residue tensor rearrangement.
A basis of the original ideal over the residue field gives a basis on every
flat test. The basis vectors are the images of the same original elements,
so their coordinates commute with the actual residue-fibre ring maps.

The descent of scalar actions uses the quotient of the original module action
through its annihilator. The flat comparison is checked on pure tensors, and
naturality of the resulting bases follows by expressing a coefficient in its
basis before applying the test-ring map.

For the flat coefficient formula, see `sga3-expose-iii-gille-polo-2024`,
Exposé III, Remarque 0.3, printed p. 114 (PDF p. 14), SHA-256
`b799de7ca975b738bdc293d703c257e63caffd6fa9365f5a398d6e01cb9599e6`.
