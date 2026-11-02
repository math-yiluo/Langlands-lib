# End homology of the finite subset Koszul complex

Author: Worker 1015.

This is an internal calculation for the finite subset Koszul complex constructed
in `FiniteKoszulCochain`. Let `R` be any commutative ring, let `g` be a natural
number, and let `a : Fin g → R`. The integer cochain complex has its subset module
of cardinality `n` in degree `g-n`.

The module on the empty subset and the module on the full subset are each
linearly equivalent to `R`, by evaluation at that subset. These give
`finiteKoszulCochainTopEquiv` and `finiteKoszulCochainZeroEquiv`, including when
`g = 0`.

At the empty subset the differential is
`x ↦ ∑ j, a j * x {j}`. Its image after evaluation is exactly
`Ideal.span (Set.range a)`: every summand belongs to that ideal, and each
generator is obtained from the corresponding singleton coordinate vector.
The differential out of degree `g` is zero by the term bound. Therefore
`finiteKoszulCochainTopHomologyIsoCokernel` identifies top homology with the
cokernel of the subset differential. The extension isomorphisms give the
commuting square used to transport this cokernel.
`finiteKoszulCochainTopHomologyIsoQuotient` then uses the module cokernel
description and the image calculation to construct

`H^g(finiteKoszulCochain a) ≅ R / Ideal.span (Set.range a)`.

For a local ring, if the parameters generate its maximal ideal,
`finiteKoszulCochainTopHomologyIsoResidueField` identifies this quotient with
`ResidueField R`.

At the other end, suppose `g = n+1`. The image of the constant vector `1` under
the first differential has, at the subset obtained by erasing `j` from the full
subset, coordinate `koszulSign R (univ.erase j) j * a j`. All its coordinates
belong to the parameter ideal. Conversely, coordinate evaluation gives the
signed generators, and the square of each sign is `1`. Its vector order ideal
is consequently the parameter ideal. For the inclusion of the order ideal in
the parameter ideal, the proof expands any vector in the finite coordinate
basis and applies the chosen linear functional. Invariance of the vector order
ideal under a linear equivalence transports the calculation to the extended
cochain complex. When `g = 0`, the first differential is zero and the parameter
ideal is zero.

Thus `finiteKoszulCochain_firstDifferentialOrderIdeal` proves the equality for
all `g`. Applying the existing first-differential cokernel calculation gives
`finiteKoszulCochainReversedDualTopHomologyIsoResidueField`: for local `R` and
parameters generating the maximal ideal, the reversed dual about degree `g`
also has residue field as its top homology.

These results use no regularity hypothesis and assert no vanishing of the
other homology modules. They are direct deductions from the existing subset
differential, its signs, categorical extension and module cokernel APIs, and
the previously established reversed-dual order-ideal criterion. No external
literature theorem is invoked in this unit.
