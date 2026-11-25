# The Hasse–Arf property for a cyclic group from congruences of depths

`Langlands.LocalFactor.Ramification.HasseArf.Counting`. The definition of the Hasse–Arf property of
a chain of subgroups, and the counting argument that proves it for the lower filtration of a group
with cyclic `G_0` from its tame and wild inputs. This is the second hard unit of the Hasse–Arf
development and has its own file.

## Statements

Name space `Langlands.Ramification`.

- The property, for a chain `Gs : ℕ → Subgroup G`:

  ```lean
  def HasseArfChain (Gs : ℕ → Subgroup G) : Prop :=
    ∀ i : ℕ, Gs i ≠ Gs (i + 1) →
      Nat.card ↥(Gs 0) ∣ ∑ j ∈ Finset.Icc 1 i, Nat.card ↥(Gs j)
  ```
  For the lower filtration, `(|G_1| + ⋯ + |G_i|) / |G_0|` is `φ(i)` (`herbrandPhiRat_natCast`), so
  the property says that `φ` takes integer values at the breaks. Two auxiliary definitions of the
  FLT file come with it: `wildSum Gs cod N = ∑_{1 ≤ i ≤ N} |Gs i| · cod (Gs i)` and
  `wildDeltaChain Gs cod N = wildSum Gs cod N / |Gs 0|`.
- The counting theorem:

  ```lean
  theorem hasseArfChain_of_isCyclic_of_dvd_of_modEq
      {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
      [PerfectField (IsLocalRing.ResidueField R)]
      [IsCyclic ↥(lowerGroup R G 0)]
      {p : ℕ} (hp : p.Prime)
      (hG1 : IsPGroup p ↥(lowerGroup R G 1))
      (hcop : ¬ p ∣ (lowerGroup R G 1).relIndex (lowerGroup R G 0))
      (htame : ∀ j : ℕ, 1 ≤ j →
        lowerGroup R G j ≠ lowerGroup R G (j + 1) →
          (lowerGroup R G 1).relIndex (lowerGroup R G 0) ∣ j)
      (hwild : ∀ σ ∈ lowerGroup R G 1, ∀ n : ℕ, 1 ≤ n → σ ^ p ^ n ≠ 1 →
        (ramificationDepth R G (σ ^ p ^ (n - 1))).toNat ≡
          (ramificationDepth R G (σ ^ p ^ n)).toNat [MOD p ^ n]) :
      HasseArfChain (lowerGroup R G)
  ```
  The hypotheses are supplied by `isPGroup_lowerGroup_one`,
  `exists_monoidHom_lowerGroup_zero_residueField_units` (`LowerGroupQuotients.lean`),
  `relIndex_dvd_of_lowerGroup_ne_succ_of_commute` (`HasseArf/Tame.lean`) and
  `ramificationDepth_pow_prime_pow_modEq_of_mem_lowerGroup_one` (`HasseArf/Congruence.lean`); see
  `HasseArf/Cyclic.lean`.

## Proof

Let `e = [G_0 : G_1]`. As `G_0` is cyclic, so is `G_1`, of order `p^m` with a generator `τ`, and
`|G_0| = e p^m` with `e` prime to `p`. Fix a break `i ≥ 1` and put `S = |G_1| + ⋯ + |G_i|`.

1. `e ∣ S`. The breaks `≥ 1` are multiples of `e` (`htame`), so the chain is constant on the blocks
   between consecutive multiples of `e` (`chain_const`), `i` is a multiple of `e`, and `S` is a sum of
   `e`-fold repeated terms (`dvd_sum_card_of_jumps_dvd`).
2. `p^m ∣ S`. Count `S` by elements: `S = ∑_g #{j ≤ i : g ∈ G_j}`, and for `g ≠ 1` the count is
   `min(i, i(g) - 1)` (`sum_card_eq_sum_card_filter`, `card_filter_mem_eq`). Elements of the same
   order in the cyclic `p`-group `G_1` generate the same subgroup and have the same depth
   (`zpowers_eq_zpowers_of_orderOf_eq`, `ramificationDepth_eq_of_zpowers_eq`); there are
   `p^(s-1)(p-1)` elements of order `p^s`, conjugate in this sense to `τ^(p^(m-s))`
   (`class_sum`). With `u_k = i(τ^(p^k)) - 1`, one of the `u_k` equals `i` (the break is the depth of
   some element of `G_1` minus one), and `hwild` gives `u_(k-1) ≡ u_k` modulo `p^k`; Abel summation
   (`abel`) then shows `p^m ∣ i + ∑_k (p^(m-k) - p^(m-k-1)) min(i, u_k) = S` (`pow_dvd_wild_sum`).
3. Since `e` and `p^m` are coprime, `|G_0| = e p^m` divides `S`.

## Declarations

In the order of the file: `wildSum`, `wildDeltaChain`, `HasseArfChain`; in
`Langlands.Ramification.HasseArf.Counting`: `Icc_one_eq_Ioc`, `chain_const`,
`dvd_sum_card_of_jumps_dvd`, `card_filter_mem_eq`, `card_filter_mem_one`,
`sum_card_eq_sum_card_filter`, `ramificationDepth_eq_of_zpowers_eq`, `ramificationDepth_le_pow`,
`zpowers_eq_zpowers_of_orderOf_eq`, `abel`, `pow_dvd_wild_sum`, `class_sum`; then
`hasseArfChain_of_isCyclic_of_dvd_of_modEq` in `Langlands.Ramification`.

## Source and licence

Adapted from three files of the Anthropic Lean formalisation of Fermat's Last Theorem (commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`; registered literature
`anthropic-flt-complete-lean-source-6e837e75`):

| FLT file | SHA-256 |
| --- | --- |
| `Definitions/Def_RamificationChain_Wild.lean` | `0a61fe8ff72f34dfd72a8f338b8565cd97083b5d0dd680da5244f203193ff678` |
| `Theorems/Thm_IsDiscreteValuationRing_hasseArfChain_of_isCyclic_of_dvd_of_modEq.lean` | `d0cd9654430fb84e46221b2f5a6b8321ab628c6059e871c66b4357c9e6efc5ac` |
| `P2M/Sol/S_IsDiscreteValuationRing_hasseArfChain_of_isCyclic_of_dvd_of_modEq.lean` | `730b199d0c6350cfdbdf2464d5039f0c976486f052f1c77d0bc10ba0e07bffa4` |

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`,
`NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. The FLT `ATTRIBUTION.md` does not
list these files as containing third-party material. The Lean file begins with an attribution
header stating that it was modified.

Changes against the FLT files: the three files are one module; `RamificationChain.HasseArfChain`,
`RamificationChain.wildSum`, `RamificationChain.wildDeltaChain` are in `Langlands.Ramification`;
the FLT proof name space `P2MW.<file>.HasseArfBook` is `Langlands.Ramification.HasseArf.Counting`;
`IsDiscreteValuationRing.hasseArfChain_of_isCyclic_of_dvd_of_modEq` is
`Langlands.Ramification.hasseArfChain_of_isCyclic_of_dvd_of_modEq`, stated on `lowerGroup` (its
statement is definitionally equal to the FLT one; the instance proofs inside differ). Deprecated
names are replaced (`ENat.toNat_coe`, `ENat.coe_toNat`, `if_pos`, `if_neg`, `SetLike.exists_of_lt` by
`ENat.toNat_natCast`, `ENat.natCast_toNat`, `ite_eq_left`, `ite_eq_right`,
`IsConcreteLE.exists_of_lt`). No options are set: the proof compiles within Lean's default limits,
so it is not split further.

## Literature

Serre, *Local Fields*, GTM 67 (1979), Chapter V, §7, Theorem 1, printed page 93 (the Hasse–Arf
theorem: for an abelian Galois group the breaks of the upper filtration are integers), and Chapter
IV, §§1–3 (lower groups, Proposition 1, printed page 62; `φ`, printed page 73). The proof here is a
counting argument in the cyclic case, from the tame divisibility of the breaks and Sen's
congruences (S. Sen, *On automorphisms of local fields*, Ann. of Math. 90 (1969), 33–46, Main
theorem, Theorem 1, printed pages 34–35; Sen's Note on printed page 37 says that for wildly ramified
cyclic extensions the Hasse–Arf theorem reduces to these congruences). Sen's `i(σ) = Ord (σ - 1)π/π`
is one less than the `ramificationDepth` of `hwild`, which does not change the congruences.
