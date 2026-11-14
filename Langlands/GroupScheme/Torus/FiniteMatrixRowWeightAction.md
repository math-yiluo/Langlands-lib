# All-test row weights of a split torus in a finite matrix algebra

This internal unit identifies the idempotent-defined division-algebra row spaces with the
character equations on points over every commutative coefficient algebra. It retains
arbitrary fields and every characteristic.

The generic finite-algebra lemma `affineUnit_inv_eq_sum` evaluates the published universal
inverse-unit expansion at an arbitrary split-torus point. Evaluation is justified by
`universalPoint_evaluateUnits` and the naturality of the actual affine unit comparison.

`rowActionOver` is inverse right multiplication by the actual coefficient unit, after the
tensor-matrix comparison. A pure matrix tensor acts on constant rows by the original
matrix. Thus the inverse-unit expansion gives the row action as the finite sum of the
monomial characters times the row projections.

Orthogonality of the published idempotents shows that a vector in `rowWeightSpace i m`
has the monomial character indexed by `m` over every coefficient algebra. Conversely,
applying the coefficient functional at `m` to its equation at the universal group-algebra
point recovers the fixed-projection equation. This proves
`mem_rowWeightSpace_iff_allTest`, including for finite ground fields.

The mathematical provenance is the published universal point, universal idempotents, and
tensor-matrix comparison, together with finite sums and coefficient extraction. This unit
supplies an action interpretation of the row decomposition; it does not establish
maximality or the multiplicities of a maximal isometry torus.
