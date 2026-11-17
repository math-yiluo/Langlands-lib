# Quotients by closed relative multiplicative-type subgroups

This internal construction proves the quotient-existence part needed for
the canonical factorization. It is derived from the affine diagonalizable
closed-subgroup quotient, relative multiplicative-type geometry and
locality, and gluing of supplied fppf quotients.

For group schemes `H` and `N` of multiplicative type over any scheme `S`,
and a closed subgroup inclusion `i : N ⟶ H`,
`exists_quotient_of_multiplicativeType` gives a group of multiplicative
type `Q` and an affine homomorphism `q : H ⟶ Q` which is the actual fppf
quotient by the full range of `i`. The definition
`closedSubgroupQuotient` chooses such a target and projection while
retaining these proofs.

There is no Noetherian, reducedness, connectedness, or nonemptiness
assumption on `S`, and no smoothness assumption on either group. The
finitely generated character groups in the relative multiplicative-type
predicate may have torsion.

The implemented proof proceeds through local models. Over an affine base
and with both groups diagonalizable, isomorphisms identify them with the
actual group-algebra models. The closed inclusion is transported to a
closed map between those models, for which the preceding construction
produces an affine fppf quotient of multiplicative type. Transport of the
compatible subgroup square gives a quotient in the original coordinates.

An affine open cover handles diagonalizable groups over an arbitrary
scheme. Next an fppf cover diagonalizes the subgroup when the source is
diagonalizable. Finally an fppf cover diagonalizes the source. At each
step the previously constructed local quotient schemes glue using the
full-kernel fppf quotient theorem, and quotient comparison on the cover
establishes multiplicative type of the resulting target.
Commutativity of the source, supplied by its multiplicative-type
structure, makes every represented subgroup range normal.

This construction assumes that the supplied subgroup is of
multiplicative type. Establishing that the kernel of the homomorphism in
the canonical factorization has this property remains a separate theorem.
