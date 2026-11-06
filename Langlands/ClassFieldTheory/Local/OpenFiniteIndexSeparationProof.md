# Separation by open finite-index subgroups

`Langlands.LocalClassField.openFiniteIndexSubgroupsSeparatePoints` proves the
published proposition `OpenFiniteIndexSubgroupsSeparatePoints` for every prime,
arbitrary carrier universe, and supplied local-field topology. Every group and
quotient in the construction is a Mathlib object on the actual field or its
integer ring. This derived internal proof uses the published unit filtration,
its structural laws, and the chosen uniformizer; it assumes no arithmetic norm
existence or reciprocity theorem.

Openness of the valuation-unit subgroup reuses
`Langlands.ClassFieldTheory.Local.isOpen_unitSubgroup` from
`NormExistenceClosedSupport`, which proves it using an open valuation sphere.
The preparatory order-kernel comparison uses the valuation-group isomorphism
and the logarithm on its nonzero values. The inclusion of integer
units into field units is an open embedding: it is induced and injective, and
its image is precisely that open valuation-unit subgroup.

Each congruence subgroup of integer units is the kernel of reduction to the
units of a finite truncated integer ring. It therefore has finite index. The
published closedness of this subgroup, together with compactness of the integer
unit group, makes it open. The open embedding then shows that every field-unit
filtration subgroup is open. The proof retains level zero, whose truncated ring
is the zero ring and whose filtration group is the valuation-unit subgroup.

For a nonidentity valuation unit, the published separation of the actual unit
filtration gives a level excluding it. Write `π` for the specified uniformizer
unit. Its normalized order is one, so the homomorphism `z ↦ π^z` splits the
order map. The homomorphism `x ↦ x / π^(ord x)` takes values in valuation units
and fixes them. Transporting it through `integerUnitsEquiv` and reducing modulo
the chosen power of the maximal ideal gives a homomorphism to a finite group.
Its kernel has finite index. It contains the open filtration subgroup at that
level, so it is open. If the original unit were in the kernel, its fixed image
under the retraction would put it in that same filtration subgroup, a
contradiction.

For an element outside the valuation-unit subgroup, reduce its order modulo
`n = |ord a| + 1`. The resulting homomorphism to the multiplicative notation for
`ZMod n` has a kernel of finite index. Its kernel contains the open
valuation-unit subgroup and is therefore open. Membership of `a` would say that
`n` divides its order. The strict absolute-value bound forces that order to be
zero, contradicting the case assumption. Combining these two cases proves the
exact supporting target.

The additional lemma
`normSubgroupsSeparatePoints_of_normSubgroupExistence` records the remaining
arithmetic implication explicitly. With `NormSubgroupExistence` as a hypothesis,
apply the proved separation to the canonical topology, realize the excluding
subgroup as the actual determinant-norm image of a finite abelian intermediate
extension in the actual algebraic closure, and rewrite subgroup membership.
Uniqueness in norm existence is unnecessary. This conditional lemma does not
prove the unconditional `NormSubgroupsSeparatePoints` target; a proof of
arithmetic norm existence is still required.
