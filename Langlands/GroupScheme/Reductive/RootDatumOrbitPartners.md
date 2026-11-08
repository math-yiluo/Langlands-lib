# Orbit partners of roots under a finite group of root-datum automorphisms

This module is combinatorics of root data and imports only Mathlib. A finite group `Γ`
acts on a finite root datum `P` through a homomorphism `ρ : Γ →* P.Aut`. The standing
hypothesis `hne : ∀ m, orbitSum P ρ m ≠ 0` says that no orbit sum of a root vanishes. This is
the situation of the absolute roots of a quasi-split group: `Γ` is a finite Galois group, and
the roots restricting to a given nonzero relative root form one orbit.

The intended use is the multipliable relative roots `a` of a quasi-split group. Take an
absolute root `p` restricting to `a`, and suppose `p + q` is a root for some other root `q`
in the orbit of `p`. The module shows that `q` is unique and pairs with `p` to exactly `-1`.
It also shows that `p` and `q` are the only decomposition of `p + q` inside the orbit, that
some element of `Γ` swaps them, and that the stabilizer of `p` has index two in the stabilizer
of `p + q`. Through the Galois correspondence, the field `E` of the root `p` is then a
quadratic extension of the field `L₀` of the root `p + q`. The last step is not made here.

Provenance: internal. The statements are the standard structure of a multipliable relative
root of a quasi-split group (the absolute roots over `a` and `2a` form a Galois-permuted
product of systems of type `A₂`). The proofs here are pairing-sum counting arguments. They
use positivity of Mathlib's canonical form `RootForm` on the root span and the Mathlib lemma
`root_sub_root_mem_of_pairingIn_pos`, and do not use the classification of root systems.

All declarations live in namespace `RootPairing.OrbitPartner`. The variables are a type
`J` of root indices, modules `M` and `N`, `P : RootDatum J M N`, a group `Γ` with
`[Fintype Γ]` (dropped by `omit` where not needed) and `ρ : Γ →* P.Aut`. Lemmas using `hne`
or `RootForm` assume `[Finite J]`.

## Definitions

- `orbitSum P ρ i = ∑ g : Γ, P.root (ρ g • i)`: the sum over `Γ` of the roots in the orbit of
  `i`, counted with stabilizer multiplicity. It is definitionally the expression
  `rootOrbitSum` of the module `Langlands.GroupScheme.Reductive.RootDatumOrbitSums`.
- `IsOrbitPartner P ρ p q`: `q` is in the orbit of `p` (`∃ g, ρ g • p = q`), `q ≠ p`, and
  `P.root p + P.root q` is a root.
- `stabilizer P ρ i : Subgroup Γ`: the preimage under `ρ` of the stabilizer of `i` in
  `P.Aut`. `mem_stabilizer_iff` says `g ∈ stabilizer P ρ i ↔ ρ g • i = i`.

## Basic transport

- `root_smul`: `P.root (ρ g • i) = ρ g • P.root i` (Mathlib
  `RootPairing.Equiv.root_indexEquiv_eq_smul`).
- `orbitSum_eq_sum_smul`: `orbitSum P ρ i = ∑ g, ρ g • P.root i`.
- `orbitSum_smul`: the orbit sum is constant on orbits (reindex by right multiplication).
- `orbitSum_eq_sub_of_root_eq_sub`, `orbitSum_eq_add_of_root_eq_add`: orbit sums are
  additive along actual root differences and sums, since each `ρ g` acts linearly.
- `pairing_smul_smul`: automorphisms preserve the pairing.
- `sum_pairing_smul_right`: `∑ g, P.pairing i (ρ g • j)` equals the orbit sum of `i`
  evaluated on the coroot of `j`. Proof: reindex by `g ↦ g⁻¹` and move `ρ g⁻¹` across the
  pairing.
- `toLinearMap_orbitSum_coroot_smul`: the orbit sum of `j` takes the same value on the
  coroots of all members of the orbit of `j`.

## Signs of pairings inside one orbit

- `sum_pairing_smul_pos hne j`: `0 < ∑ g, P.pairing j (ρ g • j)`.

  Proof. Write `x` for the orbit sum of `j` and `c` for its value on the coroot of `j`.
  Then `x` lies in the root span and is nonzero, so `0 < RootForm x x` (Mathlib
  `rootForm_pos_of_ne_zero`). Mathlib's `rootForm_self_smul_coroot` says
  `RootForm r r • r^∨ = 2 • (RootForm r)` on every root `r`. Apply it to `r = ρ g • j` and
  evaluate at `x`. With `toLinearMap_orbitSum_coroot_smul` this gives
  `2 · RootForm (ρ g • j) x = RootForm (ρ g • j) (ρ g • j) · c` for every `g`. Summing over `g`
  gives `2 · RootForm x x = S · c` with `S ≥ 0`, so `c > 0`. By `sum_pairing_smul_right`, `c`
  is the claimed sum.
- `pairing_nonpos hne`: distinct members `p ≠ q` of one orbit have `P.pairing p q ≤ 0`.
  Proof. A positive pairing makes `p - q` a root (Mathlib
  `root_sub_root_mem_of_pairingIn_pos`), and its orbit sum is
  `orbitSum p - orbitSum q = 0`, contradicting `hne`.

## Orbit partners

- `IsOrbitPartner.symm`: the relation is symmetric.
- `IsOrbitPartner.pairing_neg hne`: a partner pairs negatively. Proof. The pairing is
  `≤ 0` by `pairing_nonpos`. If it were `0`, write `m` for the root `p + q`. Then
  `P.pairing m q = 2`, so the reflection of `m` in `q` is the root `p - q`, whose orbit sum
  vanishes.
- `card_filter_smul_eq`, `sum_ite_smul_eq`: the elements of `Γ` sending `i` to a fixed member
  of its orbit form a coset of the stabilizer, so there are `s = |Stab(i)|` of them. The
  second lemma states the resulting value of a sum of an indicator over `Γ`.
- `sum_pairing_le_of_isOrbitPartner hne h`: for a partner `q` of `p`,
  `∑ g, P.pairing p (ρ g • p) ≤ (2 + P.pairing p q) · s`. Proof. Bound each term: it is `2`
  when `ρ g • p = p`, `P.pairing p q` when `ρ g • p = q`, and `≤ 0` otherwise
  (`pairing_nonpos`). Then count with `sum_ite_smul_eq`.
- `IsOrbitPartner.pairing_eq_neg_one hne`: a partner pairs to exactly `-1`. Proof. The sum is
  positive and `s ≥ 0`, so the bound forces `2 + P.pairing p q > 0`. Together with
  `pairing_neg`, the integer `P.pairing p q` lies strictly between `-2` and `0`.
- `IsOrbitPartner.unique hne`: **uniqueness of orbit partners**. Two partners `q, q'` of `p`
  are equal. Proof. If `q ≠ q'`, bounding term by term as above gives
  `0 < ∑ g, P.pairing p (ρ g • p) ≤ (2 - 1 - 1) · s = 0`.
- `IsOrbitPartner.smul`: the relation is transported by the action of `Γ`.
- `IsOrbitPartner.smul_eq_of_smul_eq hne`: the stabilizer of `p` fixes its partner (by
  transport and uniqueness).
- `IsOrbitPartner.eq_smul hne`: the partner of `ρ g • p` is `ρ g • q`.
- `IsOrbitPartner.exists_swap hne`: some `g` has `ρ g • p = q` and `ρ g • q = p`. Proof. Take
  any `g` with `ρ g • p = q`. Then `ρ g • q` is a partner of `q`, and so is `p`.

## Decompositions of the sum

In this section `m` is a root index with `P.root m = P.root p + P.root q` for a partner `q`
of `p`.

- `IsOrbitPartner.eq_or_eq_of_root_add_eq hne`: **uniqueness of partner decompositions**.
  Suppose `p', q'` are partners, `p'` is in the orbit of `p`, and
  `P.root p + P.root q = P.root p' + P.root q'`. Then `(p', q') = (p, q)` or
  `(p', q') = (q, p)`. Proof. `P.pairing m p = 2 - 1 = 1`, and this also equals
  `P.pairing p' p + P.pairing q' p`. If neither `p'` nor `q'` is `p`, both terms are `≤ 0` by
  `pairing_nonpos`. Otherwise cancel the common summand.
- `IsOrbitPartner.smul_eq_iff hne`: `ρ g • m = m` if and only if `ρ g` fixes both `p` and `q`
  or swaps them. Proof. `ρ g • p` and `ρ g • q` are partners with root sum `ρ g • P.root m`.
- `IsOrbitPartner.smul_eq_of_smul_eq_left hne`: the stabilizer of `p` fixes `m`.
- `IsOrbitPartner.exists_smul_eq_ne hne`: some element fixing `m` moves `p` (the swap).
- `IsOrbitPartner.orbitSum_eq`: `orbitSum P ρ m = 2 • orbitSum P ρ p`. This holds without
  `hne`, from additivity and `orbitSum_smul`.
- `IsOrbitPartner.stabilizer_le hne`: `stabilizer P ρ p ≤ stabilizer P ρ m`.
- `IsOrbitPartner.relIndex_stabilizer hne`:
  `(stabilizer P ρ p).relIndex (stabilizer P ρ m) = 2`. Proof. Mathlib's
  `Subgroup.relIndex_eq_two_iff` with the swap as the element of `Stab(m) \ Stab(p)`. By
  `smul_eq_iff`, each `b ∈ Stab(m)` fixes or swaps `p` and `q`, and exactly one of `b` and
  `s b` fixes `p`.

## Existence of decompositions

- `exists_root_eq_add_of_orbitSum_eq_two_nsmul hne`: if
  `orbitSum P ρ m = 2 • orbitSum P ρ p`, there are `g : Γ` and a root index `q` with
  `P.root m = P.root (ρ g • p) + P.root q` and `orbitSum P ρ q = orbitSum P ρ p`.

  Proof. By `sum_pairing_smul_right`, `∑ g, P.pairing m (ρ g • p)` is twice the positive sum
  of `sum_pairing_smul_pos`. So some term `P.pairing m (ρ g • p)` is positive, and
  `m ≠ ρ g • p` (otherwise `orbitSum p = 0`). Mathlib's `root_sub_root_mem_of_pairingIn_pos`
  makes `q = m - ρ g • p` a root, and its orbit sum is `orbitSum p` by additivity.

  The lemma does not claim that `q` lies in the orbit of `p`. In the application, roots with
  equal restriction form one orbit (transitivity on fibers of the restriction), which puts
  `q` in the orbit. That transitivity is not part of this module.
- `isOrbitPartner_of_root_eq_add hred`: assume no root `i` has `P.root i + P.root i` a root
  (`hred`, a reducedness condition). Then a member `q` of the orbit of `p` with
  `P.root p + P.root q` a root is an orbit partner of `p`: the condition `q ≠ p` follows from
  `hred`. This lemma does not use `hne` or finiteness of `Γ`.
