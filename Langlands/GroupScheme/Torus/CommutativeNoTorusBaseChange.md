# Commutative groups without tori under field extension

Author: Worker 1467.

This internal deduction combines the published geometric cocharacter vanishing
and specialization results. The target group is an affine commutative group
scheme locally of finite type over an arbitrary field; smoothness and
connectedness are not assumed.

`CocharacterDatum.gm_hom_eq_zero_of_no_torus` assumes every homomorphism from
every base-field torus to the group has bottom subgroup-functor range. It proves
that every cocharacter of the actual group-scheme base change to any extension
field is zero. Geometric cocharacter vanishing first gives zero cocharacters
over the algebraic closure of the base field. Embed that algebraic closure into
the algebraic closure of the extension field; the published algebraically closed
specialization theorem gives zero cocharacters after this further extension.
The natural isomorphism comparing the two iterated scheme pullbacks transports
this to the algebraic closure of the extension, and faithful field pullback
reflects the equality of the original cocharacter with zero.

The argument is a derived composition of Library theorems, including
`gm_hom_eq_zero_over_algebraicClosure`,
`CocharacterSpecialization.gm_hom_eq_zero_of_baseField`,
`algebraicClosureBaseChangeIso`, and
`GaloisCocharacterDescent.baseChangeCocharacter_injective`. It assumes no
unproved structural proposition.

`CocharacterDatum.torus_hom_eq_zero_of_no_torus` extends the conclusion to
every homomorphism from every extension-field torus. Choose a field over which
that torus splits, and equip it with the composite algebra structure over the
original field. The field-tower base-change isomorphism identifies the twice
extended target with its direct extension. Each coordinate inclusion of the
split source followed by the transported homomorphism is a cocharacter, so the
first lemma kills it. The decomposition
`splitTorus.sum_proj_comp_single` of the identity as the sum of coordinate
projections followed by inclusions then kills the entire homomorphism.
Cancelling the comparison isomorphisms and applying the faithfulness of field
pullback gives zero before the splitting extension.

`CocharacterDatum.range_eq_bot_of_no_torus` restates this equality as bottom
subgroup-functor range on every scheme test. The source torus need not descend
to the original field, and the extension has no separability, algebraicity, or
finiteness assumption. The target retains only affineness, local finite type,
and commutativity.
