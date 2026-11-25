# Cohomological dimension of a local field, vanishing and finiteness

`Langlands/GaloisCohomology/Local/Dimension.lean`, namespaces `Langlands.GaloisCohomology` and
`Langlands.GaloisCohomology.Local`.

For a nonarchimedean local field `K` with separable closure `Ksep` and a prime `ℓ` invertible in
`K`, the `ℓ`-cohomological dimension of `Gal(Ksep/K)` is at most `2`. Consequences: vanishing of
`Hʳ` for `r ≥ 3` on torsion modules of order invertible in `K`, and finiteness of all `Hʳ` for
finite modules of order invertible in `K`.

## Declarations

- `eq_zero_of_primaryComponent_eq_bot`: an element killed by `n ≠ 0` vanishes when all its
  `ℓ`-primary components for `ℓ ∣ n` do.
- `rootsOfUnityFixing_normal`, `rootsOfUnityFixingNormal`: the subgroup fixing `μ_n` is normal (the
  first for any integral extension `E/F`).
- `apply_eq_of_isProPGroup`: for an integral extension `E/F` with `Gal(E/F)` compact and totally
  disconnected (here `Ksep/K`), a pro-`ℓ` subgroup of `Gal(E/F)` fixes the `ℓ`-th roots of unity of
  `E`.
- `nonempty_zmod_addEquiv_rootsOfUnity`: `μ_ℓ(Ksep) ≅ ℤ/ℓ` for `ℓ` prime, invertible in `K`.
- `cd_le_two K Ksep hℓ hℓK : cd ℓ Gal(Ksep/K) ≤ 2` for `ℓ` prime with `(ℓ : K) ≠ 0`. A pro-`ℓ`
  Sylow subgroup `P` fixes `μ_ℓ ≅ ℤ/ℓ`, so `H³(P, ℤ/ℓ)` is a direct summand of `H³(P, μ_ℓ)`; a class
  of the latter is restricted from an open subgroup `U ⊇ P`, where `H³(U, μ_ℓ) = 0`.
- `subsingleton_cohomology_res_of_three_le hn U M hM hr`: for `n` invertible in `K` and a smooth
  `n`-torsion module `M` of an open subgroup `U`, `Hʳ(U, M) = 0` for `r ≥ 3`;
  `subsingleton_cohomology_of_three_le hn M hM hr`: the same for `Gal(Ksep/K)`.
- `finite_cohomology_res hn U M hM r`: every `Hʳ(U, M)` is finite for a finite smooth `n`-torsion
  module; `finite_cohomology K Ksep M hM r`: every `Hʳ(Gal(Ksep/K), M)` is finite for a finite
  smooth module `M` with `(Nat.card M : K) ≠ 0`.
- `hasFiniteCohomology_res U`, `hasFiniteCohomology`: `Gal(Ksep/K)` and its open subgroups satisfy
  `HasFiniteCohomology` for the modules of order invertible in `K` (the hypothesis of the
  abstract Euler characteristic).

The hypothesis `(ℓ : K) ≠ 0` cannot be dropped from `cd_le_two` as stated: for `ℓ` the
characteristic of `K` the cohomological dimension is `1`, which is not proved here.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files
`src/GroundTheory/ProfiniteCohomology/LocalClassFormation/FiniteVanishing/Vanishing.lean`
(`eq_zero_of_primaryComponent_eq_bot`, `rootsOfUnityFixing_normal`, `rootsOfUnityFixingNormal`,
`apply_eq_of_isProPGroup`, `nonempty_zmod_addEquiv_rootsOfUnity`, `cdp_galois_le_two` (here
`cd_le_two`), `subsingleton_cohomology_of_three_le` (here
`subsingleton_cohomology_res_of_three_le`)) and `LocalClassFormation/FiniteVanishing.lean`
(`finite_cohomology_galois`, `subsingleton_cohomology_galois_top`, `finite_cohomology_galois_top`,
`hasFiniteCohomology_galois`, `hasFiniteCohomology_galois_top`: here `finite_cohomology_res`,
`subsingleton_cohomology_of_three_le`, `finite_cohomology`, `hasFiniteCohomology_res`,
`hasFiniteCohomology`). The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`).

The source's `FiniteVanishing/{FormationThree, TateThree, IntScalars}.lean` (vanishing of `H³` of
a class formation through the source's Tate cohomology over `ℤ`) are not taken: the foundations'
`ClassFormation.subsingleton_cohomology_of_three_le`, on the Library's Tate theorem, replaces them.
The source states its theorems for `K Ksep : Type`; they are stated here for `K Ksep : Type u`, and
`rootsOfUnityFixing_normal`, `apply_eq_of_isProPGroup` for any integral extension `E/F` in place of
a separable closure.

## References

- J.-P. Serre, *Galois Cohomology*, chapter II, §5.3, Proposition 15 (`scd = 2`; for `p`-adic
  fields), p. 93.
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, chapter VII, §1, Theorem
  (7.1.8), p. 376, and §2, Theorem (7.2.9), p. 383.
