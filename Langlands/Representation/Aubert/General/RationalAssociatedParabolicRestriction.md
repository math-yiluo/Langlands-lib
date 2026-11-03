# Associated rational restricted parabolic and unipotent transport

This internal derived construction restricts the actual associated-Levi
continuous group equivalence to the literal restricted parabolic and
unipotent families. For a target standard subset `J`, let
`J' = associatedSubset cs J`, take `K : Finset J'`, and put
`Kt = associatedFinsetEquiv cs J K`. The two equivalences are

```text
(P_(leviIndex J Kt)).subgroupOf M_J
  ≃ₜ* (P_(leviIndex J' K)).subgroupOf M_J',
(U_(leviIndex J Kt)).subgroupOf M_J
  ≃ₜ* (U_(leviIndex J' K)).subgroupOf M_J'.
```

Their maps on underlying rational points are `x ↦ n⁻¹ * x * n`, for
every actual point-normalizer lift `n` whose class is `longestRep cs J`.
Their inverses are `x ↦ n * x * n⁻¹`, using that same supplied lift.
The ambient and subgroup topologies are the actual ones.

The field is arbitrary. The ambient group scheme is affine and connected
reductive, the inclusion is a maximal split torus and monomorphic on schemes,
and the given cocharacter is generic. The simple-root labels and actual
point Weyl quotient have supplied finite enumerations. The normalizer and
full-centralizer comparisons, root-length and positive-simple-reflection
comparisons, minimality criterion and associated-subset laws are exactly
those of the rational compatibility target. Standard cocharacters are
obtained from its `StandardCocharacterStatement`. No full scheme Coxeter
realization is assumed. Empty root sets and all standard subsets are allowed.
The continuous equivalences additionally use a topological group structure
on the rational points and `StandardLeviConjugationStatement` to construct
the same ambient associated-Levi equivalence used by the target.
No local compactness, characteristic or local-field restriction is needed.

The proof of `weylAction_image_associatedSubset` applies the actual longest
character automorphism to the inverse-image formula
`rootSet_associatedSubset`. The automorphism and its inverse cancel. The
normalizer comparison rewrites this as the scheme-normalizer character action
without changing the underlying rational point.
The fine-set image is the published
`weylAction_image_associatedFinsetEquiv`.

`associatedRestrictedParabolic_unipotent_mem` supplies both actual membership
equivalences inside the target coarse Levi. Finiteness of the simple-root set
follows by reading the finite set of all simple labels as characters.
The two coarse standard-cocharacter witnesses are the existence clauses of
`StandardCocharacterStatement`. The literal fine subsets lie inside their
coarse subsets by `leviIndex_subset` and `rootSet_subset_iff`.
The generic all-test theorem
`mem_standardParabolic_unipotent_inv_conj_iff_of_character_images` now
applies at the identity test scheme with these two character-image equations.
`constantPoint_self` evaluates its conjugating point as the original `n`.

The definitions `associatedRestrictedParabolicEquiv` and
`associatedRestrictedUnipotentEquiv` apply `GroupTransport.subgroupEquiv`
to `associatedLeviConjugationEquiv` and the corresponding membership law.
Their application and inverse-application formulas follow from those
constructors.

Provenance is internal: the new results specialize the imported actual
character-image and orbit-extension transport proofs to the weaker point
Coxeter hypotheses already present in the rational target. No representation
comparison, K0 equation, geometric expansion or Haar-modulus factorization
is assumed or proved here. These remain separate parts of the full Jacquet
compatibility argument.
