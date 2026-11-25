# The Euler–Poincaré characteristic

`Langlands/Cohomology/Profinite/EulerCharacteristic.lean`, namespace
`Langlands.ProfiniteCohomology`.

For a smooth module `A` with finite cohomology, `χ(A) = |H⁰(G, A)| · |H²(G, A)| / |H¹(G, A)|`.
For a group whose cohomology with coefficients in finite modules (of orders in a class `P`) is
finite and vanishes from degree `3` on, `χ` is multiplicative in short exact sequences, hence
factors through the Grothendieck group of such modules; and `χ` of a coinduced module equals `χ`
of the module of the open subgroup. This is the frame of Tate's local Euler characteristic
formula, which belongs to the local theory.

## Declarations

- `finiteDiscreteRep k G P`: the smooth finite representations whose order satisfies `P`;
  `grothendieckRelations`, `GrothendieckGroup k G P` (free abelian group on them modulo
  `[A₂] - [A₁] - [A₃]` for short exact sequences), `GrothendieckGroup.mk`.
- `HasFiniteCohomology k G P`: for every smooth finite `A` of order in `P`, all `Hᵠ(G, A)` are
  finite and they vanish for `q ≥ 3`.
- `eulerCharacteristic A`: the rational number `∏_{q<3} |Hᵠ(G, A)|^{(-1)^q}`;
  `eulerCharacteristic_eq`: it is `|H⁰| · |H²| / |H¹|`.
- `card_eq_card_ker_mul_card_range`, `card_range_eq_card_ker_of_exact`: counting along linear
  maps and exact sequences.
- `eulerCharacteristic_shortExact_of_finite`: for a short exact sequence with finite `H¹`'s and
  `H³(A₁) = 0`, `χ(A₂) = χ(A₁) χ(A₃)`. `eulerCharacteristic_pos`; `eulerCharacteristic_shortExact_of_mem`
  and `eulerCharacteristic_shortExact` (when `P` is closed under divisors it suffices that `A₂` is
  finite of order in `P`).
- `eulerCharacteristicUnit`, `coe_eulerCharacteristicUnit`, `eulerCharacteristicHom`: `χ` as a
  homomorphism from the Grothendieck group to `ℚˣ`.
- For an open subgroup `U` of a compact group: `eulerCharacteristic_coind` (`χ_G(Coind B) = χ_U(B)`,
  by Shapiro's lemma), `eulerCharacteristic_res_eq_eulerCharacteristic_coind`; `coindValues`,
  `coindValues_injective`, the instance `finite_coind` and `card_coind_dvd`
  (`|Coind B|` divides `|B|^{[G:U]}`); `coindValues_surjective` (`coindValues U B` is onto: a
  function on `G/U` is the restriction of an element of the coinduced module, through chosen
  representatives) and `card_coind U B : Nat.card (Rep.coind (U : Subgroup G).subtype B) =
  Nat.card B ^ (U : Subgroup G).index` for finite `B` and finite `G/U`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files
`src/GroundTheory/ProfiniteCohomology/EulerCharDefs.lean` and
`src/GroundTheory/ProfiniteCohomology/EulerChar.lean`. The repository has no licence file; its
text is used with attribution
(`licenses/RiemannHypothesis/SOURCE.md`). Names: the source's `eulerChar` is
`eulerCharacteristic`, and `eulerChar` → `eulerCharacteristic` in all names (`eulerCharUnit` →
`eulerCharacteristicUnit`, `eulerCharHom` → `eulerCharacteristicHom`, `eulerChar_coind` →
`eulerCharacteristic_coind`, …); the other names are the source's. `coindValues_surjective` and
`card_coind` are not from the source.

## References

- J.-P. Serre, *Galois Cohomology* (English translation of *Cohomologie galoisienne*, Springer 1997;
  corrected printing 2002), chapter II, §5.4, pp. 93–94 (`χ(A) = h⁰(A)h²(A)/h¹(A)` for a finite
  `G_k`-module, `k` a `p`-adic field, and its multiplicativity in exact sequences, p. 94).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter VII, §3, pp. 391–392 (the local Euler–Poincaré characteristic,
  its multiplicativity, and Tate's Theorem (7.3.1), p. 392).
