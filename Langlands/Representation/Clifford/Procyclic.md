# Groups with procyclic quotient by a normal subgroup

This internal module collects the group theory of a topological group `G`
with a subgroup `N` such that every commutator lies in `N` (so `N` and every
subgroup containing it are normal and `G / N` is abelian) and, for every open
subgroup `U` containing `N`, the powers of one element meet every right coset
of `U` (so `G / U` is cyclic). Inertia of a local field over its wild
inertia subgroup is the motivating example (J.-P. Serre, *Local Fields*
(1979), registered as `serre-1979-local-fields`, IV §2, Corollaries 1–4 to
Proposition 7, printed pp. 67–68). The module defines the tame characters and
compares the tame characters of an open subgroup `H ⊇ N` with those of `G`
through the power map `x ↦ x^[G : H]`.

## Commutators and indices

- `CommutatorsIn N` says `x * y * x⁻¹ * y⁻¹ ∈ N` for all `x, y`. Under it,
  every subgroup containing `N` is normal (`normal_of_le`), and
  `(x * y)^n` agrees with `x^n * y^n` modulo `N` for every integer `n`
  (`mul_zpow_mem`).
- `zpow_mem_iff_dvd`: if every element is congruent to a power of `g` modulo a
  subgroup `U` contained in a normal subgroup `V`, then `g^i ∈ V` exactly when
  `V.index` divides `i`. The class of `g` generates `G / V`, so its order is the
  index.

## Tame characters

- `CyclicOpenQuotients N` says: for every open subgroup `U ⊇ N` there is
  `g ∈ G` with every `x` congruent to a power of `g` modulo `U`.
- `tameCharacters N H` is the set of homomorphisms `H →* ℂˣ` that are trivial
  on `N ∩ H` and have open kernel; `tameCharactersTop N` is the same set for
  `G`.
- `le_iff_index_dvd`: in a topological group, under `CommutatorsIn N` and
  `CyclicOpenQuotients N`, for open subgroups `U, V ⊇ N`, `U ≤ V` exactly when
  the index of `V` divides that of `U`. A common generator modulo `U ∩ V` reduces
  this to `zpow_mem_iff_dvd`.

## Power characters

From here on `CommutatorsIn N` is assumed. Fix a subgroup `H ⊇ N`; it is
normal and `x^[G:H] ∈ H` for all `x` (`pow_index_mem'`).

- `powChar hab hNH χ hχ` is `x ↦ χ (x^[G:H])` for a character `χ` of `H`
  trivial on `N`. It is a homomorphism because `(xy)^n` and `x^n y^n` differ
  by an element of `N` (`powChar_apply` gives the value).
- `powChar_comp_restrictAut`: for an automorphism `α` of `G` preserving `H`,
  the power character of `χ ∘ α|_H` is the power character of `χ` composed
  with `α`. `powChar_congr` rewrites along an equality of characters, and
  `powChar_mem_tameCharactersTop` shows that power characters of tame
  characters are tame.
- `powChar_injective`: under `CyclicOpenQuotients N` and for `H` open, two
  tame characters of `H` with the same power character agree. Choose a generator `g` modulo the open subgroup
  `ker χ ∩ ker χ'`; every element of `H` is congruent to a power
  `g^([G:H] t)` modulo that subgroup, on which both characters are given by
  the common power character at `g^t`.
- `exists_powChar_eq`: in a topological group, under `CyclicOpenQuotients N`
  and for `H` open, every tame character `ψ` of `G` is a power character of a
  tame character of `H`, provided `p ≠ 1`, every open subgroup containing `N`
  has index prime to `p`, and for every `d` prime to `p` there is an open
  subgroup containing `N` of index `d`. Take such a subgroup `U` of index
  `[G : H] · [G : ker ψ]`; by `le_iff_index_dvd` it lies in `H` and in
  `ker ψ`. With a generator `g` modulo `U`, an element of `H` congruent to
  `g^i` has `[G : H] ∣ i`, and `χ` is defined as `ψ (g^(i / [G:H]))`. This is
  well defined because two exponents differ by a multiple of
  `[G : U] = [G : H] · [G : ker ψ]`.
