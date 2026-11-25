# Finite group theory for splitting arguments

Module `Nyll.GaloisCohomology.GroupTheory.Finite`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file collects three pieces of finite group theory used in field-theoretic splitting arguments: subgroups of index p in p-groups, elements of prime order, and a criterion with double cosets for a subgroup to lie in the normal core of another.

## Main results

- `exists_index_prime_supergroup_of_card_prime_power`: if G is finite of order `p^v` with p prime and v > 0, every proper subgroup D lies in a subgroup P of index p. Cyclicity is not assumed.
- `cyclic_exists_normal_index_prime_supergroup`: if moreover G is cyclic, P can be taken normal with `|G/P| = p`.
- `subgroup_le_index_prime_subgroup_of_ne_top_cyclic_prime_power`: in a cyclic group of order `p^e`, every proper subgroup lies in every subgroup of index p.
- `exists_element_of_prime_order` and `exists_cyclic_subgroup_of_prime_card`: a nontrivial finite group has an element of prime order p, hence a cyclic subgroup of order p.
- `doubleCosetRightProjection H D` is the map `Hg ↦ HgD` from the cosets of H, written as double cosets `H\G/1`, to the double cosets `H\G/D`; it is surjective.
- `rightSubgroup_le_normalCore_of_doubleCoset_projection_injective`: if this map is injective, D lies in the normal core of H. `rightSubgroup_le_normalCore_of_doubleCoset_card_eq`: for G finite, the same follows from equality of the numbers of double cosets and of cosets.
- `doubleCoset_card_eq_leftCoset_iff_of_normalCore_eq_bot`: for G finite and H with trivial normal core, `|H\G/D| = |H\G|` exactly when D is trivial.

## Proof

The first result uses Mathlib's Sylow-type theorem `Sylow.exists_subgroup_card_pow_prime_le`, which gives a subgroup of order `p^(v−1)` containing D. In the cyclic case, a generator g and the description of subgroups as `⟨g^n⟩` show that a proper subgroup has n divisible by p, so its generator is a p-th power and lies in any subgroup of index p. Elements of prime order come from Cauchy's theorem in Mathlib. For double cosets, if `HgD = HgdD` forces `Hg = Hgd`, then `gdg⁻¹ ∈ H` for all g.

## Watch for

- Double cosets are Mathlib's `DoubleCoset.Quotient`, and the cosets `Hg` (called left cosets in the file) are encoded as double cosets with trivial right subgroup, not as the quotient `G ⧸ H`.
- In the cyclic-supergroup statement, cyclicity is used only to make P normal; the index-p statement holds for every finite p-group.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/GroupTheory/Finite.lean`: the Lean file is the source byte for byte (SHA-256 `47bf9d6daefa578e23848742168856e5c1f79378a83574333f8a1847edfb67f9`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
