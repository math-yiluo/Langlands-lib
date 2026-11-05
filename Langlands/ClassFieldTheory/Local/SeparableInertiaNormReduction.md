# Unit norm surjectivity for a finite Galois extension

Author: Worker 1512. This is the third helper module of the proof of
`Langlands.ClassFieldTheory.Local.SeparableInertiaUnitNormSurjectivity` (see
`SeparableInertiaNormProof.md`). It imports `SeparableInertiaNormCyclic` and
Mathlib (`Polynomial.Taylor`, `GroupTheory.IndexNormal`, `GroupTheory.Sylow`).
All declarations are in `Langlands.ClassFieldTheory.Local.SeparableInertiaNorm`.

## Field lemmas

Let `K` be a field with `v : Valuation K ℝ≥0`.

- `IntPoly.derivative`, `IntPoly.hasseDeriv`: derivatives and Hasse derivatives
  of integral polynomials are integral.
- `val_eval_sub_le`: on integral elements, an integral polynomial satisfies
  `v (f a - f b) ≤ v (a - b)`. The proof factors each `a ^ i - b ^ i` by
  `geom_sum₂_mul`.
- `eq_of_eval_eq_zero` (uniqueness of simple roots): let `f` be integral, `a`
  integral with `f a = 0` and `v (f' a) = 1`, and `b` a root with
  `v (b - a) < 1`. Then `b = a`. The proof expands `f` at `a` with `taylor`:
  `0 = f(b) = (b - a) (f'(a) + (b - a) S)` with `v S ≤ 1`. If `b ≠ a`, then
  `f'(a) = -(b - a) S` has value `< 1`, which is a contradiction.
- `valHensel_comap` (Galois descent of Hensel lifting): let `L / K` be a field
  extension and `w` a valuation on `L` with `ValHensel w`. Assume `w` is
  invariant under `L ≃ₐ[K] L` and every element fixed by all these
  automorphisms lies in `K`. Then `ValHensel (w.comap (algebraMap K L))`. Proof:
  lift the Hensel root `a` of `f` in `L`. For every `σ`, `σ a` is a root close
  to `a`, and `f'(a)` is a unit (by `val_eval_sub_le`). So `σ a = a` by
  `eq_of_eval_eq_zero`, and `a` lies in `K`.
- `valResidueRoot_comap` (ascent of root finding): let `K → B → L` be a tower
  and `w` a valuation on `L`. Assume root finding over `K` and that every
  integral element of `L` is congruent to an integral element of `K`. Then
  root finding holds over `B`. Proof: replace each coefficient of
  `f : B[X]` by a congruent coefficient in `K`, find a root modulo the maximal
  ideal over `K`, and compare the two evaluations term by term.
- `exists_valUniformizer`: assume `0 < q < 1`, `D > 0` and that every nonzero
  integral `x` has `v x ^ D = q ^ k` for some `k`. If some `c` has
  `0 < v c < 1`, then `v` has a uniformizer. It is an element `π` with the least
  positive exponent `n0`, chosen by `Nat.find`. For integral `b ≠ 0` with
  `v b ^ D = q ^ k`, write `k = n0 j + r`. Minimality forces `r = 0`, so
  `v b = v π ^ j`.

## Towers

`cyclicHyp_of_tower`: let `B → C → M` be a tower with `M / B` normal and
`w : Valuation M ℝ≥0`. Assume Galois invariance over `B`, `[C : B]` prime,
Hensel lifting, root finding and a uniformizer for `w` restricted to `B`, and
the congruence property of `M` over `B`. Then `CyclicHyp (w.comap (algebraMap C M)) π`
holds. Invariance under `Gal(C/B)` follows by extending automorphisms to `M`
(`AlgEquiv.liftNormal_commutes`).

## The reduction hypotheses

`M / E` is a finite Galois extension and `w : Valuation M ℝ≥0`. The structure
`ReductionHyp w p` (an internal interface) bundles:

- `inv`: invariance of `w` under `Gal(M/E)`;
- `prime`, `natCast`: `p` is prime and `w (m : M) = 1` whenever `p ∤ m`;
- `hensel`: `ValHensel w` on `M`;
- `residueRoot`: root finding for `w` restricted to `E`;
- `res`: every integral element of `M` is congruent to an integral element
  of `E`;
- `disc`: there are `D > 0` and `0 < q < 1` such that every nonzero integral
  `x : M` has `w x ^ D = q ^ k` for some `k`;
- `small`: some `c : E` has `0 < w c < 1`.

From these, for every intermediate field `B` of `M / E`: `inv_of`, `hensel_of`
(by `valHensel_comap`), `henselE`, `res_of`, `residueRoot_of` (by
`valResidueRoot_comap`) and `unif_of` (by `exists_valUniformizer` applied to `c`).
`cyclic` combines them with `cyclicHyp_of_tower` and
`CyclicHyp.exists_norm_eq`. For an intermediate field `B` and a Galois
subextension `C / B` of prime degree, every unit of `B` is the norm of a unit
of `C`.

## The main argument

- `pgroup`: if `[M : B] = p ^ k`, every unit of `B` is the norm of a unit of `M`.
  The proof is by induction on `k`. For `k + 1`, `Sylow.exists_subgroup_card_pow_prime`
  gives a subgroup `H` of `Gal(M/B)` of order `p ^ k`. It has index `p`, which
  is the least prime factor of the group order, so `H` is normal
  (`Subgroup.normal_of_index_eq_minFac_card`). With `C = M ^ H`, the extension
  `C / B` is Galois of degree `p`. A unit `u` of `B` is `N_{C/B} x` (by
  `cyclic`), and `x` is `N_{M/C} z` (induction hypothesis for `C`, viewed as an
  intermediate field over `E`, with `Algebra.norm_eq_of_ringEquiv`). Then
  `Algebra.norm_norm` gives `N_{M/B} z = u`.
- `exists_pow_eq`: if `p ∤ m`, every unit `u` of `E` is `y ^ m` for a unit `y`
  of `E`. Root finding for `X ^ m - u` gives an approximate root `b` with
  `w b = 1`. The derivative `m b ^ (m - 1)` has value `1` by `natCast`, so
  `henselE` gives an exact root.
- `ReductionHyp.exists_norm_eq`: every unit `u` of `E` is the norm of a unit of
  `M`. Write `[M : E] = p ^ a m` with `p ∤ m`. Take a Sylow subgroup `H` of
  order `p ^ a` and `B = M ^ H`, so `[B : E] = m`. Write `u = y ^ m` with `y` a
  unit of `E`, and apply `pgroup` to `y` over `B`. Then
  `N_{M/E} z = N_{B/E}(y) = y ^ m = u`.

## Relation to the literature

This is the "dévissage" of Serre, *Local Fields* (literature ID
`serre-1979-local-fields`), Chapter V, §4, proof of Proposition 7 (printed
p. 90, PDF p. 97). There, solvability of the Galois group of a totally
ramified extension reduces the problem to cyclic extensions of prime degree.
The Lean proof does not assume total ramification and uses only Sylow
theory. The prime-to-`p` part is handled by extracting `m`-th roots with
Hensel's lemma, and the `p`-part by a chain of normal subgroups of index `p`.
