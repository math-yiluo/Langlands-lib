# Subgroup criterion for a three-factor rank-one base cell

This internal group-theoretic deduction works in any group `G`. For subgroups
`U,V,Z`, `baseSubgroup` is their supremum `U ⊔ V ⊔ Z`. Assume that
conjugation by every element of `Z` preserves `U` and `V`,
and that every product `a*b`, with `a ∈ U` and `b ∈ V`, admits factors in the
order `V Z U`. Then the set product `V Z U` equals the carrier of `U ⊔ V ⊔ Z`.
All three conditions are explicit premises; this module makes no assertion
about their validity for root filtrations.

The implemented proof shows that `V Z U` contains the identity and is stable
under right multiplication by each of the three subgroups. Right `U`
multiplication combines the last factors. Right `Z` multiplication conjugates
the last `U` factor by the inverse of the new `Z` element. Right `V`
multiplication applies the assumed exchange to the last `U` factor and the
new `V` factor, then conjugates the resulting `V` factor across the existing
`Z` factor. The same arguments apply to inverses of generators. Subgroup
closure induction gives the forward containment, and the reverse follows
from the three canonical inclusions in the supremum. This is an internal
algebraic prerequisite for the base cell of KP Lemma 7.1.5(3).
