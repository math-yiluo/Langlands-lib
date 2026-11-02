# Actual GL parabolic quotients and ambient subgroup bridges

Author: Worker 585.

This internal construction supplies concrete group maps for the general-to-GL
Aubert specialization. It reuses the actual upper block parabolic, diagonal
projection, radical kernel, Levi embedding and conjugation action of
`Langlands.Group.GL.Blocks`, together with the normalizer theorem in
`Langlands.Group.GL.OppositeBlocks`. It introduces no replacement group model.

The algebraic declarations work over any commutative ring `R : Type uR`,
for every natural rank `n` and positive ordered block shape `B`. Rank zero
is included: the existing empty-block conventions apply without a
positive-rank assumption.

`unipotentAmbientEquiv` identifies the radical inside the parabolic with
its actual image inside GL by the injective parabolic inclusion.
`leviSubgroup_le_parabolic` and `unipotentSubgroup_le_parabolic` give the
two concrete inclusions. `leviSubgroup_inf_unipotentSubgroup` proves their
intersection is the identity subgroup: the Levi projection is one on
the radical and is the identity on the Levi section.
`parabolic_eq_unipotent_mul_levi` uses the already proved `u*m`
decomposition, and `parabolic_eq_levi_mul_unipotent` uses the existing
Levi normalizer theorem to reverse the product order. These are equalities
of actual subsets of GL.

`parabolicQuotientLevi` is a multiplicative equivalence from the actual
quotient of the parabolic by its normal unipotent radical to the product
Levi. Mathlib's first isomorphism construction uses the existing
diagonal-block projection and its explicit block-diagonal right inverse.
Its forward formula on every quotient representative is
`parabolicQuotientLevi_mk`; its inverse is the class of the Levi section,
as stated by `parabolicQuotientLevi_symm_apply`.
`unipotentAmbientEquiv_leviAction` computes the existing radical action
as ordinary conjugation by the ambient block-diagonal matrix.

With a Hausdorff topological ring structure,
`unipotentAmbientEquivContinuous` identifies the actual subgroup
topologies as well. `isClosed_leviSubgroup` proves closedness by expressing
the Levi section's range inside the parabolic as the fixed set of its
continuous projection followed by section. The already closed parabolic
inclusion then gives closedness in GL.

This unit has no representation-theoretic or classification prerequisites.
It does not construct the shared general reductive datum, identify relative
root subgroups, compare modulus characters, compare normalized functors,
or identify Aubert operators. Those are further specialization obligations.
In particular, the group quotient equivalence here is algebraic; the
topological equivalence asserted in this unit is the radical inclusion.
