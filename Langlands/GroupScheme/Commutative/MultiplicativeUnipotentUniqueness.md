# Uniqueness of a multiplicative-unipotent decomposition

This internal derived unit proves the uniqueness clause of Milne 2017,
Theorem 16.13(b). Let `k` be a field and `G` a commutative group scheme over
`Spec k` that is affine and locally of finite type. Suppose `u : U ⟶ G` and
`s : S ⟶ G` are subgroups such that the multiplication map
`subgroupMultiplication u s : U × S ⟶ G` is an isomorphism.

- `range_le_of_isMultiplicativeType`: if `u` is a closed subgroup and `U` is
  unipotent, then every subgroup `h : H ⟶ G` with `H` of multiplicative type
  has range inside the range of `s`. This lemma does not need `h` to be a
  closed immersion, and it does not use that `G` is locally of finite type.
- `range_le_of_isUnipotent`: if `S` is of multiplicative type, then every
  unipotent closed subgroup `j : V ⟶ G` has range inside the range of `u`.

The lemmas do not need perfectness of `k`.

## Route

1. **Homomorphisms from unipotent to multiplicative type vanish**
   (`hom_eq_zero_of_isUnipotent_of_isMultiplicativeType`). Let `V` be affine,
   locally of finite type and unipotent, `S` of multiplicative type, and
   `f : V ⟶ S`. The Library's `affineHomImage` factors `f` as an fppf
   quotient `q : V ⟶ I` followed by a closed subgroup `i : I ⟶ S`. The image
   `I` is unipotent, as a quotient of a unipotent group
   (`IsFppfQuotient.isUnipotent`). It is of multiplicative type, as a closed
   subgroup of `S` (`IsMultiplicativeType.of_isClosedSubgroup`). By Milne
   14.18 (`IsMultiplicativeType.hom_eq_zero_of_isUnipotent`), the identity of
   `I` is zero, so `f = q ≫ 𝟙 ≫ i = 0`.
2. **The decomposition gives a group retraction.** In a commutative group
   any two subgroups commute (`commute_of_isCommMonObj`). The Library's
   `commutingSubgroupMultiplicationHom u s` is a group homomorphism
   `U × S ⟶ G` whose underlying morphism is `subgroupMultiplication u s`.
   `isIso_commutingSubgroupMultiplicationHom` shows it is an isomorphism of
   groups when the multiplication map is an isomorphism, using that the
   forgetful functors from groups to monoids and from monoids to objects
   reflect isomorphisms. The Library's `commutingFactorRetraction u s` is the
   resulting projection `G ⟶ U`. A point of `G` lies in the range of `s`
   exactly when its projection to `U` is trivial
   (`comp_commutingFactorRetraction_eq_one_iff`).
3. **Containment** (`range_le_of_comp_commutingFactorRetraction`). If
   `h ≫ commutingFactorRetraction u s = 0`, then every point of the range of
   `h` lies in the range of `s`.
4. **Multiplicative part.** For `H` of multiplicative type, the composite
   `H ⟶ U` is zero by 14.18, since `U` is affine (a closed subgroup of
   affine `G`) and unipotent.
5. **Unipotent part.** Multiplication is symmetric in a commutative group
   (`subgroupMultiplication_swap`), so `subgroupMultiplication s u` is also
   an isomorphism. Then step 3 with the roles of `U` and `S` exchanged applies
   to `j : V ⟶ G`. The composite `V ⟶ S` is zero by step 1, since `V` is
   affine and locally of finite type as a closed subgroup of `G`.

## Provenance

The statement is the uniqueness part of Milne, *Algebraic Groups* (2017),
Theorem 16.13(b). Milne derives it from the vanishing of homomorphisms
between unipotent groups and groups of multiplicative type (Corollary 14.18
and its consequence for images). Step 1 is an internal formalization of that
vanishing in the direction unipotent to multiplicative type. It uses the
Library's image factorization together with 14.18. The retraction argument
is internal and uses the Library's `CommutingFactorRetraction` module.
