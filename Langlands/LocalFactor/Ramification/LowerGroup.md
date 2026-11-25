# Lower ramification groups of an action on a local ring

`Langlands.LocalFactor.Ramification.LowerGroup`. For a group `G` acting by ring automorphisms on a
commutative local ring `R` with maximal ideal `m`, the Library's `lowerGroup R G i`
(`Filtration.lean`) is the subgroup of elements acting trivially on `R ⧸ m ^ (i + 1)`; the same
file proves that the groups decrease (`lowerGroup_antitone`), are normal (`lowerGroup_normal`) and
that `lowerGroup R G 0` is the inertia group of `m` (`lowerGroup_zero`). This module adds the
membership criterion, the zeroth group as the kernel of the action on the residue field, the
triviality of the intersection of all lower groups, and the lower groups of a subgroup.

## Statements

All declarations are in the name space `Langlands.Ramification`; `R` is a commutative local ring,
`G` a group with `[MulSemiringAction G R]`.

- Membership (a `simp` lemma, true by definition):

  ```lean
  theorem mem_lowerGroup {i : ℕ} {σ : G} :
      σ ∈ lowerGroup R G i ↔ ∀ x : R, σ • x - x ∈ (IsLocalRing.maximalIdeal R) ^ (i + 1)
  ```
- The zeroth group is the kernel of the action on the residue field:

  ```lean
  theorem lowerGroup_zero_eq_ker :
      lowerGroup R G 0 =
        MonoidHom.ker (MulSemiringAction.toRingAut G (IsLocalRing.ResidueField R))
  ```
  and every lower group lies in it (`lowerGroup_le_zero`).
- If the powers of the maximal ideal meet in zero and the action is faithful, the lower groups
  meet in the trivial group:

  ```lean
  theorem iInf_lowerGroup_eq_bot (hsep : ⨅ n, (IsLocalRing.maximalIdeal R) ^ n = ⊥)
      [FaithfulSMul G R] :
      ⨅ i, lowerGroup R G i = (⊥ : Subgroup G)
  ```
  (without faithfulness the intersection lies in the kernel of the action,
  `iInf_lowerGroup_le_ker_toRingAut`). The Library's `iInf_congruenceGroup` (`Filtration.lean`)
  proves the same for a Noetherian `R`, where `hsep` is Krull's intersection theorem.
- For a subgroup `H`, the lower groups of the restricted action are `G_i ∩ H`:

  ```lean
  theorem lowerGroup_subgroupOf (H : Subgroup G) (i : ℕ) :
      (lowerGroup R G i).subgroupOf H = lowerGroup R H i
  theorem lowerGroup_map_subtype (H : Subgroup G) (i : ℕ) :
      (lowerGroup R H i).map H.subtype = lowerGroup R G i ⊓ H
  ```
  More generally, for a homomorphism `f : H →* G` with `f h • x = h • x`,
  `lowerGroup R H i = (lowerGroup R G i).comap f` (`lowerGroup_comap_of_forall_smul_eq`).
- Two facts on inertia groups of ideals: `inertia_mono` (`I ≤ J` gives
  `I.inertia G ≤ J.inertia G`) and `inertia_normal_of_forall_smul_eq` (the inertia group of an
  ideal stable under `G` is normal); and the `simp` lemmas `pointwise_smul_maximalIdeal`,
  `pointwise_smul_maximalIdeal_pow` (`g • m ^ n = m ^ n`).

## Proofs

Everything is unfolding of the definition: `σ ∈ lowerGroup R G 0` says that `σ` acts trivially on
`R ⧸ m`, which is the residue field; an element of every lower group moves every `x` into
`⋂ m ^ n = 0`, hence acts as the identity, and faithfulness makes it `1`; the restricted action of
`H` has the same condition on its elements, so its lower groups are `G_i ∩ H` by `rfl`. The
pointwise lemmas say that a ring automorphism maps the maximal ideal of a local ring onto itself.

## Declarations

In the order of the file: `inertia_mono`, `inertia_normal_of_forall_smul_eq`,
`pointwise_smul_maximalIdeal`, `pointwise_smul_maximalIdeal_pow`, `mem_lowerGroup`,
`lowerGroup_zero_eq_ker`, `lowerGroup_le_zero`, `iInf_lowerGroup_le_ker_toRingAut`,
`iInf_lowerGroup_eq_bot`, `lowerGroup_comap_of_forall_smul_eq`, `mem_lowerGroup_subgroup`,
`lowerGroup_subgroupOf`, `lowerGroup_map_subtype`, `lowerGroup_map_subtype'`,
`lowerGroup_subgroup_eq_top_iff`, `lowerGroup_comap_inclusion`,
`lowerGroup_map_subtype_le_map_subtype`.

## Source and licence

Adapted from two files of the Anthropic Lean formalisation of Fermat's Last Theorem (commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`; registered literature
`anthropic-flt-complete-lean-source-6e837e75`):

| FLT file | SHA-256 |
| --- | --- |
| `Definitions/Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup.lean` | `f8db223941b714c707b057398f4fa5b99cc38f2b47fab4103a1a91f02e2e7689` |
| `Definitions/Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupSubgroup.lean` | `fa80a6898dc9335dc7df8537916b4c305f89dc76c37ede4d5be1b4da79963dd9` |

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`,
`NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. The FLT `ATTRIBUTION.md` does not
list these files as containing third-party material. The Lean file begins with an attribution
header stating that it was modified.

Changes against the FLT files:

- The FLT definition `IsLocalRing.lowerRamificationGroup R G i` is the same subgroup as the
  Library's `lowerGroup R G i`; every statement is on `lowerGroup`. The FLT lemmas
  `lowerRamificationGroup_antitone`, `lowerRamificationGroup_normal` and
  `lowerRamificationGroup_zero_eq_inertia` are `lowerGroup_antitone`, `lowerGroup_normal` and
  `lowerGroup_zero` of `Filtration.lean` (with `R`, `G` explicit there) and are not repeated.
- Upstream's `IsLocalRing.X` and `Ideal.X` are `Langlands.Ramification.X` with
  `lowerRamificationGroup` read as `lowerGroup` (for example
  `IsLocalRing.iInf_lowerRamificationGroup_eq_bot` is `iInf_lowerGroup_eq_bot`).
- The `ValuationSubring` versions of the FLT files (for the decomposition group of a valuation
  subring) are not kept: nothing in the Library uses them. The FLT file's copy of
  `AddSubgroup.inertia_mono`, now in Mathlib, was already absent from the extract.
- The example blocks and `#print axioms` checks are not kept; no options are set.

## Literature

Serre, *Local Fields*, GTM 67 (1979), Chapter IV, §1: the lower ramification groups of a finite
Galois extension of local fields as the elements acting trivially on the quotients of the ring of
integers (Lemma 1, printed page 61), their normality and decrease and `G_0` as the inertia group
(Proposition 1, printed page 62), and `H_i = G_i ∩ H` for a subgroup `H` (Proposition 2, printed
page 62). Serre's setting is a complete discretely valued field with separable residue extension
(printed page 61); here `G` is any group acting on a commutative local ring.
