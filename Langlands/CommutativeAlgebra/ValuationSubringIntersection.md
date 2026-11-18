# Finite intersections of valuation subrings

Module `Langlands.CommutativeAlgebra.ValuationSubringIntersection` (imports Mathlib only).
All declarations below are in the namespace
`Langlands.CommutativeAlgebra.ValuationSubringIntersection`.

## Setting

`K : Type u` is a field and `V : ι → ValuationSubring K` is a family of valuation subrings
indexed by `ι : Type v`. `A : Subring K` is any subring with

```
hA : ∀ x, x ∈ A ↔ ∀ i, x ∈ V i,
```

so `A` is the intersection of the `V i`. No incomparability or distinctness hypothesis on the
`V i` is assumed anywhere. The main results need `[Finite ι]`, and the result on maximal
ideals also needs `[Nonempty ι]`. The universes `u`, `v` and the universe `w` of the local
rings `S` below are independent.

## Definitions

* `toValuationSubring V hA i : A →+* V i` is the inclusion `A ⊆ V i`, as the
  codomain restriction of `A.subtype`. Its values have underlying element `a`
  (`coe_toValuationSubring`, by `rfl`).
* `prime V hA i : Ideal A` is the preimage of the maximal ideal of `V i` under
  `toValuationSubring V hA i`. It is prime (instance `prime_isPrime`), and
  - `mem_prime : a ∈ prime V hA i ↔ (V i).valuation a < 1`,
  - `not_mem_prime : a ∉ prime V hA i ↔ (V i).valuation a = 1`.

## Main results

1. `isLocalization_atPrime [Finite ι] (i)`. Let `S : Type w` be a commutative `A`-algebra and
   `j : S →+* K` an injective ring map with `j (algebraMap A S a) = a` for all `a : A` and with
   image exactly `V i` (`∀ y, y ∈ V i ↔ ∃ s, j s = y`). Then
   `IsLocalization.AtPrime S (prime V hA i)`. Here `S` can be a local ring of a scheme, embedded
   into its function field, whose image is `V i`.
2. `isLocalization_atPrime_valuationSubring [Finite ι] (i)`: the special case `S = V i`, with
   the algebra structure given by `toValuationSubring V hA i` and `j = (V i).subtype`.
3. `exists_eq_prime_of_isMaximal [Finite ι] [Nonempty ι] (M) [M.IsMaximal] : ∃ i, M = prime V hA i`.
   So every maximal ideal of `A` is the contraction of the maximal ideal of some `V i`.
4. `exists_isLocalization_atPrime_of_isMaximal [Finite ι] [Nonempty ι] (M) [M.IsMaximal]`
   combines 1 and 3. Its inputs are a family `S : ι → Type w` of commutative rings, ring maps
   `κ i : A →+* S i`, and injective `j i : S i →+* K` with `j i (κ i a) = a` and image `V i`.
   It gives `∃ i, letI := (κ i).toAlgebra; IsLocalization.AtPrime (S i) M`.
5. `isFractionRing [Finite ι] : IsFractionRing A K`, for the canonical algebra structure of the
   subring `A` on `K`. This includes the case of empty `ι`, where `A = K`.

Two auxiliary lemmas are also exported:

* `exists_mem_mul_mem [Finite ι] (x : K)`: there is `s : K` such that `s ∈ V i` and `x * s ∈ V i`
  for every `i`, `(V i).valuation s = 1` whenever `x ∈ V i`, and `s ≠ 0` if `ι` is nonempty.
* `not_le_of_ne`: if `W, W'` are valuation subrings of `K` with `[Ring.KrullDimLE 1 W]` (for
  example discrete valuation rings), `W ≠ W'` and `W' ≠ ⊤`, then `¬ W ≤ W'`. This follows
  directly from Mathlib's `ValuationSubring.eq_self_or_eq_top_of_le`. It is provided for callers
  that need incomparability of distinct discrete valuation rings; none of the results above
  use it.

## Proof

The key step is a geometric-sum trick. For `x : K` and a natural number `p`, put
`f = ∑_{n<p} x^n`.

* `prime_eq_of_geomSum_eq_zero`: in a nontrivial commutative ring `k`, if `∑_{n<p} a^n = 0`
  and `∑_{n<q} a^n = 0` for primes `p ≠ q`, then `a^p = a^q = 1` (by `geom_sum_mul`), so
  `a = 1` since `p, q` are coprime. Then `p = q = 0` in `k`, so `ringChar k` divides
  `gcd p q = 1`, which is impossible. Hence such a prime `p` is unique.
* `geomSum_valuation_lt_one_subsingleton`: applying this in the residue field of a valuation
  subring `W ∋ x`, at most one prime `p` makes `f` a non-unit of `W`.
* `exists_prime_geomSum_valuation_eq_one`: with finitely many `V i`, only finitely many primes
  are bad for some `V i ∋ x`. Since there are infinitely many primes, some prime `p` makes `f`
  a unit of every `V i` that contains `x`.
* `exists_mem_mul_mem`: take `s = f⁻¹` for that `p`. If `x ∈ V i`, then `v_i(f) = 1`. If
  `x ∉ V i`, then `v_i(x) > 1`, so `v_i(x - 1) = v_i(x)` and `v_i(x^p - 1) = v_i(x)^p`.
  From `f (x - 1) = x^p - 1` we get `v_i(f) = v_i(x)^(p-1) ≥ v_i(x) > 1`, using `p ≥ 2`. In
  both cases `1 ≤ v_i(f)` and `v_i(x) ≤ v_i(f)`, so `s` and `x s` lie in `V i`.

The main results are deduced as follows.

* Localization (`isLocalization_atPrime`), checked through Mathlib's `isLocalization_iff`:
  - An element `a ∉ prime V hA i` has `v_i(a) = 1`. So `a⁻¹ ∈ V i = j(S)`, and
    `algebraMap A S a` is a unit by injectivity of `j`.
  - For `z : S`, let `y = j z ∈ V i` and take `s` from `exists_mem_mul_mem` for `y`. Then
    `s, y s ∈ A`, `s ∉ prime V hA i`, and `z · s = y s` in `S`.
  - `algebraMap A S` is injective because `j ∘ algebraMap A S` is the inclusion `A ⊆ K`.
* Maximal ideals (`exists_eq_prime_of_isMaximal`): an element `a` of `M` that lies in no
  `prime V hA i` has `v_i(a) = 1` for every `i`. So `a ≠ 0` (here `ι` is nonempty) and
  `a⁻¹ ∈ A`, which would make `a` a unit in `M`. Hence `M ⊆ ⋃ i, prime V hA i`. Prime avoidance
  (`Ideal.subset_union_prime_finite`) gives `M ≤ prime V hA i` for some `i`, and maximality
  gives equality.
* Fraction field (`isFractionRing`, via `IsFractionRing.of_field`): if `z ∈ A` then `z = z / 1`.
  Otherwise `z ∉ V i` for some `i`, so `ι` is nonempty, and `z = (z s) / s` with `z s, s ∈ A`,
  `s ≠ 0`.

## Provenance

This module is derived content supporting Bosch–Lütkebohmert–Raynaud, *Néron Models* (1990),
§6.4 Lemma 4 (printed p. 155, PDF p. 162; literature ID
`bosch-lutkebohmert-raynaud-1990-neron-models`). In the proof of that lemma the local rings
`O_{X,x_i}` at the finitely many codimension-one points are discrete valuation rings in the
function field `L`. The book then states that `A = ⋂ O_{X,x_i}` "is a semi-local ring with local
components `O_{X,x_i}`", citing the approximation theorem for inequivalent valuations
(Bourbaki, *Commutative Algebra*, Chap. VI, §7, no. 1, Prop. 1).

This module formalizes the part of that claim used to build an affine model with these local
rings. Every maximal ideal of `A` is the contraction of some `O_{X,x_i}`, each `O_{X,x_i}` is
the localization of `A` at its contraction, and `L` is the fraction field of `A`. The same
statement, for finitely many arbitrary valuation rings, is Matsumura, *Commutative Ring
Theory*, Theorem 12.2. That source is not in the project literature, so it is named only for
orientation. The Lean proof does not use the approximation theorem. It uses the
geometric-sum argument above, which needs no incomparability hypothesis. Accordingly, the
module does not claim that the primes `prime V hA i` are pairwise distinct, that each of them is
maximal, or that `A` is noetherian.
