# Local Tate duality

`Langlands/GaloisCohomology/Local/Duality/Main.lean`, namespace `Langlands.GaloisCohomology.Local`.

**Theorem (Tate, Poitou).** For a finite smooth `Gal(Ksep/K)`-module `M` of order invertible in
`K`, the Tate pairing `Hʳ(M) × Hˢ(M') → ℚ/ℤ`, `r + s = 2`, `M' = Hom(M, Ksepˣ)` the Cartier dual,
is perfect (`tatePairing_bijective`, `tatePairing_flip_bijective`).

`Pairing.lean` proves this under the counting hypothesis `CardCohomologyOneLe`:
`|H¹(U, μ_n)| ≤ |H¹(U, ℤ/n)|` for open `U` and `n` invertible in `K`. It is proved here from the
Euler characteristic formula. By Shapiro's lemma and `|Coind_U^G B| = |B|^{[G:U]}`, the Euler
characteristic of a finite module of `U` depends only on its order, so `χ(U, μ_n) = χ(U, ℤ/n)`.
Since `|H²(U, μ_n)| = n = |H⁰(U, ℤ/n)|`, the inequality becomes `|H⁰(U, μ_n)| ≤ |H²(U, ℤ/n)|`. The
`n`-th roots of unity fixed by `U` are the `m`-th roots of unity, `m` their number; then
`ℤ/m ≅ μ_m` as `U`-modules, `|H²(U, ℤ/m)| = |H²(U, μ_m)| = m`, and `H²(U, ℤ/n) → H²(U, ℤ/m)` is
onto because `H³(U, ℤ/(n/m)) = 0`.

## Declarations

- `|Coind_U^G B| = |B|^{[G:U]}` is `card_coind` of `Langlands.Cohomology.Profinite.EulerCharacteristic`.
- `eulerCharacteristic_res_eq K Ksep U B hB`: the Euler characteristic of a module of `U` from its
  order.
- `card_cohomology_zero_zmodRep`, `fixedRootsOfUnity n U` (the `n`-th roots of unity fixed by `U`),
  `card_cohomology_zero_rootsOfUnity`, `finite_fixedRootsOfUnity`, `fixedRootsOfUnity_eq`.
- `zmodMulHom`, `zmodMulAdd`, `zmodReduceAdd`, `zmodSequence G h` (`0 → ℤ/k → ℤ/n → ℤ/m → 0`,
  `n = mk`), `zmodSequence_shortExact`.
- `card_cohomology_zero_le_card_cohomology_two hn U : |H⁰(U, μ_n)| ≤ |H²(U, ℤ/n)|`.
- `cardCohomologyOneLe K Ksep : CardCohomologyOneLe K Ksep`.
- `tatePairing_bijective K Ksep M hM h`, `tatePairing_flip_bijective K Ksep M hM h`.

## Source and licence

New file. The source (repository `leanprover-community/riemann-hypothesis`, commit `f1f6d65`,
`src/GroundTheory/ProfiniteCohomology/LocalTateDuality/TensorHomDualRepRootsOfUnityIsoCartierPairing.lean`,
`bijective_localDualityPairing`, `bijective_localDualityPairing_flip`) proves duality with the
existence theorem of local class field theory; here the counting replaces it, and the proofs
contain no text of the source.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, chapter VII, §2, Theorem
  (7.2.6) (Tate duality, stated for `p`-adic fields), p. 380, and §3, Theorem (7.3.1), p. 392.
- J.-P. Serre, *Galois Cohomology*, chapter II, §5.2, Theorem 2, p. 91, and §5.7, Theorem 5, p. 99
  (for `p`-adic fields).
