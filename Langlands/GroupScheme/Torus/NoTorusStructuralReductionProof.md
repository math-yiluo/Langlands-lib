# The conditional structural reduction for no-torus unipotence

Author: Worker 1487.

`Langlands.GroupScheme.noTorusStructuralReduction.{u}` proves exactly
`NoTorusStructuralReductionStatement.{u}`. The theorem is conditional on
the six structural propositions listed in that statement; it does not
supply their proofs or an unconditional proof of the parent theorem.
This is an internal assembly proof using the published actual-point
interfaces.

First the all-homomorphism hypothesis implies absence of nontrivial closed
tori. For a finite ground field, the existing conditional finite-field
reduction applies geometric maximal-torus existence and the algebraically
closed trivial-maximal-torus implication.

For an infinite ground field, the proof uses strong induction on the
dimension of the actual dual-number Lie kernel. The induction property is
unipotence for smooth connected affine groups having no nontrivial closed
tori. The isogeny reduction supplies a target group, either nilpotent or
having a geometric noncentral semisimple tangent element, and lifts its
closed tori up to torus isogeny. The latter property transfers the absence
of closed tori to the target.

In the nilpotent branch, nilpotence reflects through the finite
homomorphism to the original group. Its absence of closed tori and the
conditional central-torus structure theorem then give unipotence.

In the other branch, the rational-existence conclusion of the spanning
premise supplies a semisimple tangent element with proper tangent
centralizer over the ground field. The proof takes an actual closed
representative of this centralizer. Its smoothness is supplied by the
smoothness premise. Its identity component has strictly smaller Lie
dimension. The isogeny preserves the Lie dimension of the two smooth
affine groups, so this component is also smaller than the original
induction group. It inherits absence of closed tori, hence is unipotent
by induction.

The original tangent element is nonzero: the tangent centralizer of zero
(written `1` in the multiplicative actual-kernel notation) is the entire
Lie module. The nonunipotence adapter lifts this nonzero semisimple
element into the smooth centralizer's identity component and contradicts
its unipotence. That adapter restricts a faithful ambient representation,
combining nilpotence of unipotent tangent matrices with their ambient
semisimplicity. No reflection of semisimplicity along a subgroup
homomorphism is needed. No assertion about preservation of maximal tori
by the centralizer inclusion is used.

Only the existence portion of the spanning premise is needed in this
proof. Every field and structural proposition remains at the arbitrary
universe `u`; finite fields are handled explicitly.
