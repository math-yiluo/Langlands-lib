# Actual transporter differences and the orbit of a torus range

This internal construction uses actual inner automorphisms and subgroup functors
on all schemes over an arbitrary base scheme B. It is intended as the algebraic
input for changing torus apartment charts; no building or topology is constructed.

The source and target commutative group schemes need not be tori. If actual
transporters g and h identify the embedded source i with the embedded target j
through isomorphisms e_g and e_h, their difference h inverse times g normalizes i.
Its source automorphism is e_g followed by e_h inverse. No monomorphism, field,
reductivity, splitness or conjugacy existence premise is used for this implication.

Base points act on the existing SubgroupFunctor G by pullback along Int(g inverse).
Thus the action is actual forward conjugation: x belongs to g acting on F exactly
when g inverse times x times g belongs to F, with base points pulled back to the
test scheme. The action is on subgroup functors, not just subgroups of base points.
Its stabilizer is the published all-test normalizer evaluated at the base.

For a monomorphic underlying scheme map i from a commutative group scheme,
`torusRangeOrbitEquivQuotient` identifies the orbit of SubgroupFunctor.range i with
the set G(B)/normalizerPoints i of left cosets gN. Its inverse on the coset of g is
the literal all-test range of i followed by Int(g). This uses the published
`torusNormalizer_carrier_base` and Mathlib's orbit-stabilizer equivalence.
The quotient is a set quotient of groups of points and has no quotient-group
structure asserted; it is not identified with points of a sheaf quotient.

The derivation is internal: category composition and the published actual inner
isomorphism formulas give the transporter difference, and the universal normalizer
condition is equivalent to stabilization of the full subgroup functor. Mathlib's
general orbit-stabilizer theorem then applies. Worker 118 identified this exact
interface for apartment indexing; the algebraic construction retains its original
objects. Existence or conjugacy of maximal split tori, the cross-torus root/weight
comparison, and affine apartment/valuation transport are separate obligations.
