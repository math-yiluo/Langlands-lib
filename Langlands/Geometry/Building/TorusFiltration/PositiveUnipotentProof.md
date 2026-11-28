# Unipotence of positive-depth minimal congruent models

`minimalCongruentPositiveUnipotent` proves
`MinimalCongruentPositiveUnipotentStatement` for every smooth model
realizing the minimal congruent point group of a torus over
`inertiaFixedField F` at a strictly positive depth. The integral base
is `fixedFieldIntegers F`. Its residue field is algebraically closed
by `fixedFieldResidueIsAlgClosure`. Write \(p\) for its characteristic.

The proof first shows that the special-fibre points of the realizing
model are killed by powers of \(p\). Henselian lifting and injectivity
of `IntegralModel.integralPointMap` give commutativity on these points
from the commutativity of the generic torus. The subset killed by
powers of \(p\) is thus a subgroup. For the first congruence subgroup
of a smooth model, `IntegralModel.pow_mem_congruenceSubgroupAt_succ`
puts its \(p\)-th powers in the second congruence subgroup. This is
the first congruence subgroup of the first congruence model by
`IntegralModel.congruenceSubgroupAt_positiveCongruenceModel`.
The generic identity extends from the first congruence model to any
realizing model containing its points, and the extension preserves
first congruence. At depth \(r\ge1\), `minimalCongruentCongruence`
applies this argument to the constructed model at depth \(r-1\).

At \(0<r<1\), the same argument handles the first congruence term of
the connected Néron model. Each other generator comes from an induced
torus. `InducedTorusShallow.exists_model_reduction_pPower` supplies
its smooth shallow model and the power property for reductions.
`exists_hom_of_map_integralPoints_le` extends its generating morphism
to the realizing model. `IntegralModel.Hom.reduction_naturality` then
carries the power property to the image. The subgroup property and
surjectivity of reduction finish the calculation on all residue points.

In any representation over the residue field, a matrix killed by a
\(p\)-power has nilpotent difference from the identity. This follows
from `sub_pow_char_pow_of_commute` applied to the matrix and the
identity. `perfectFieldUnipotentRationalPoints` and
`isIso_of_forall_rationalPoint_factors` give scheme unipotence from
these matrix identities on rational points of the smooth affine fibre.

The result is the unipotence assertion used in Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Proposition B.10.12 and
Corollary B.10.14, printed pp. 691–692, PDF pp. 722–723. The induced
models come from Proposition B.3.6, printed pp. 658–659, PDF
pp. 689–690. See `RadicalStatement` for the scope of the assertion.
The source is `kaletha-prasad-2023-bruhat-tits-new-approach`,
SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
