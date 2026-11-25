# Supernatural numbers and the index of a closed subgroup

`Langlands/Cohomology/Profinite/Dimension/Supernatural.lean`, namespace
`Langlands.ProfiniteCohomology`.

A supernatural number is a formal product `∏ p^{n_p}` over the primes with exponents
`n_p ∈ {0, 1, 2, …, ∞}`. The index of a closed subgroup `H` of a profinite group `G` is the
supernatural number `sup_U [G : H U]` over the open normal subgroups `U`. It is the measure of
size used by the theory of cohomological dimension (Sylow subgroups, `cd_p` of subgroups).

## Declarations

- `Supernatural`: functions from the primes to `ℕ∞` (the exponents), with `mk`, `exp`, `ext`,
  the complete lattice structure (`le_def`: comparison exponent by exponent; `exp_iSup`:
  exponents of a supremum), and the commutative monoid structure in which exponents add
  (`exp_one`, `exp_mul`). `dvd_iff_le`: divisibility is the order.
- `Supernatural.ofNat n`: the supernatural number of a natural number (exponents given by the
  factorization). It sends `1` to `1` and products of nonzero numbers to products
  (`ofNat_one`, `ofNat_mul`), and on nonzero numbers it reflects divisibility and equality
  (`ofNat_dvd_ofNat`, `ofNat_injective`). `ofNat_prime_dvd_iff`: `p` divides `a` iff the exponent
  of `p` in `a` is at least `1`; `ofNat_prime_dvd_iSup_iff`: `p` divides a supremum iff it
  divides one of its terms. `iSup_mul_iSup`: for directed families, the product of the suprema
  is the supremum of the products.
- Lemmas on subgroups and a normal subgroup `U` (of finite index where needed):
  `inf_sup_normal_eq` (`X ⊓ (H ⊔ U) = (X ⊓ H) ⊔ U` when `U ≤ X`), `relIndex_sup_normal_eq`,
  `index_sup_normal_eq_mul` (`[G : K U] = [G : H U] · [H U : K U]` for `K ≤ H`),
  `sup_subgroupOf_eq`.
- `superIndex H`: the supremum over the open normal subgroups `U` of `ofNat [G : H U]`;
  `superRelIndex K H`: the supernatural index of `K ∩ H` in `H`.
- Instance `OpenNormalSubgroup.finiteIndex` (an open normal subgroup of a compact group has
  finite index), `index_sup_ne_zero`, `relIndex_sup_ne_zero`, and the antitonicity of
  `U ↦ ofNat [G : H U]` and of `U ↦ ofNat [H : K U]` (`ofNat_index_sup_antitone`,
  `ofNat_relIndex_sup_antitone`).
- `not_dvd_superIndex_iff`: `p` does not divide the supernatural index of `H` iff it divides
  none of the finite indices `[G : H U]`.
- For a compact totally disconnected group: `superRelIndex_eq_iSup` (the relative index as a
  supremum of the finite relative indices `[H : K U]`), `superIndex_of_isOpen` (for an open
  subgroup the supernatural index is the ordinary index), `superIndex_eq_mul`
  (`(G : K) = (G : H)(H : K)` for `K ≤ H`) and `superIndex_dvd_of_le`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files
`src/GroundTheory/ProfiniteCohomology/Supernatural.lean` and
`src/GroundTheory/ProfiniteCohomology/OfNatRelIndexSupAntitone.lean`. The repository has no
licence file; its text is used with attribution
(`licenses/RiemannHypothesis/SOURCE.md`). Names are the source's, in the namespace
`Langlands.ProfiniteCohomology` instead of `GroundTheory.ProfCoh`.

## References

- J.-P. Serre, *Galois Cohomology* (English translation of *Cohomologie galoisienne*, Springer 1997;
  corrected printing 2002), chapter I, §1.3, p. 5 (supernatural numbers, the index `(G : H)`,
  Proposition 2: `(G : K) = (G : H)(H : K)`).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter I, §1, Definition (1.1.5), p. 6 (supernatural numbers), and
  Definition (1.1.6), p. 7 (index and order).
