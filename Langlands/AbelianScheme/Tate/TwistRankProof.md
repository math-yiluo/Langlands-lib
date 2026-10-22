# Proof that the actual integral Tate twist has rank one

This module proves the published statement
`Langlands.TateTwist.IntegralRankOne` from
`Langlands.AbelianScheme.Tate.TwistRankStatement`. The theorem is

```lean
theorem Langlands.TateTwist.integralRankOne (Ω : Type u) [Field Ω] (p : ℕ)
    [Fact p.Prime] : IntegralRankOne Ω p
```

Given a field `Ω` and a prime `p`, if `Ω` is separably closed and
`(p : Ω) ≠ 0`, there is a `ℤ_[p]`-linear equivalence
`ℤ_[p] ≃ₗ[ℤ_[p]] Langlands.TateTwist.Integral Ω p`. The statement and its
imports are unchanged. The proof adds no hypotheses and uses no `sorry`
and no new axioms. Helper declarations are in the namespace
`Langlands.TateTwist.RankOne`.

## Scope

The equivalence is algebraic and noncanonical. It depends on a chosen
compatible system of primitive roots of unity, made with `Classical.choose`
and the existence lemma below. The module does not claim that the
equivalence commutes with the automorphism or Galois actions on the twist,
and it proves nothing about continuity or topology. The source
(Edixhoven, van der Geer and Moonen, *Abelian Varieties*, Chapter X (10.8))
is cited by the statement module. This proof uses the elementary route
below rather than following a proof from the literature.

## Compatible primitive roots

Throughout, `Ω` is separably closed and `NeZero (p : Ω)` holds. In the
main theorem this instance comes from the hypothesis `(p : Ω) ≠ 0`.

* `tower ζ` is a sequence of successive `p`-th roots that starts at `ζ`:
  `tower ζ 0 = ζ`, and `tower ζ (n + 1)` is a chosen root of
  `X ^ p = tower ζ n`. The root exists by `IsSepClosed.exists_pow_nat_eq`,
  which needs `p` to be nonzero in `Ω`. `tower_succ_pow` records
  `tower ζ (n + 1) ^ p = tower ζ n`.
* `root ζ n = tower ζ n ^ p`. By `root_succ_pow`,
  `root ζ (n + 1) ^ p = root ζ n`.
* `tower_isPrimitiveRoot`: if `ζ` is a primitive `p`-th root of unity, then
  `tower ζ n` is a primitive `p ^ (n + 1)`-th root of unity. The proof
  is by induction. The order of `tower ζ (n + 1)` divides `p ^ (n + 2)`
  but not `p ^ (n + 1)`, because raising it to the `p ^ (n + 1)`-th power
  gives `tower ζ n ^ (p ^ n)`. That power is not `1`, because
  `tower ζ n` is primitive of order `p ^ (n + 1)` by the induction
  hypothesis. Mathlib's `orderOf_eq_prime_pow` then gives the order.
* `root_isPrimitiveRoot`: `root ζ n` is a primitive `p ^ n`-th root of
  unity, since it is the `p`-th power of a primitive `p ^ (n + 1)`-th root.
  The `root` sequence starts at `root ζ 0 = 1`, so level `0` (the trivial
  group of `1`-st roots of unity) is covered without a special case.

## Generators of the actual levels

`generator hζ n : Level Ω (p ^ n)` is `root ζ n`, viewed as an element of
the published level `Additive (rootsOfUnity (p ^ n) Ω)` through
`IsPrimitiveRoot.toRootsOfUnity`. The following lemmas are about these
generators.

* `generator_val` gives the underlying field element, and
  `zmod_smul_generator_val` gives the underlying element of
  `k • generator hζ n`, for `k : ZMod (p ^ n)`, as `root ζ n ^ k.val`.
  The second uses the published `toUnit_zmod_smul`.
* `transition_generator`: the published power-by-`p` transition from level
  `p ^ (n + 1)` to level `p ^ n` sends `generator hζ (n + 1)` to
  `generator hζ n`. This follows from `toUnit_transition_succ` and
  `root_succ_pow`.
* `eq_zero_of_zmod_smul_generator`: if `k • generator hζ n = 0`, then
  `k = 0`. The proof uses primitivity: `root ζ n ^ k.val = 1` forces
  `p ^ n ∣ k.val`.
* `exists_zmod_smul_generator`: every `x : Level Ω (p ^ n)` equals
  `k • generator hζ n` for some `k`. The proof uses
  `IsPrimitiveRoot.eq_pow_of_pow_eq_one`.

So each actual level is a free `ZMod (p ^ n)`-module of rank one, with
generator `generator hζ n`, and these generators are compatible under the
published transitions.

## The comparison map

`toIntegral hζ : ℤ_[p] →ₗ[ℤ_[p]] Integral Ω p` is built with the published
universal property `Langlands.TateTwist.lift`. Its level-`n` component is
`LinearMap.toSpanSingleton` of `generator hζ n`. These components are
compatible by `transition_smul` and `transition_generator`.
`evaluation_toIntegral` holds by definition: the `n`-th coordinate of
`toIntegral hζ a` is `PadicInt.toZModPow n a • generator hζ n`.

* `toIntegral_injective`: if `toIntegral hζ a = 0`, then every residue
  `PadicInt.toZModPow n a` vanishes by `eq_zero_of_zmod_smul_generator`.
  So `a = 0` by `PadicInt.ext_of_toZModPow`.
* `toIntegral_surjective`: given `x : Integral Ω p`, choose `k n` with
  `k n • generator hζ n = evaluation Ω p n x`. Coherence of `x`, together
  with `transition_zmod_smul` and `transition_generator`, shows that
  `k (n + 1)` reduces to `k n`, again by the uniqueness lemma. Hence the
  integers `(k i).val` satisfy `p ^ i ∣ (k (i + 1)).val - (k i).val`.
  Mathlib's `PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub` turns them into a
  `p`-adic integer `PadicInt.ofIntSeq`. By
  `PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub`, its residue modulo `p ^ n`
  is `k n`. So its image has the same coordinates as `x`.

## Main theorem

`integralRankOne` assumes `IsSepClosed Ω` and `(p : Ω) ≠ 0`. From these
it gets `NeZero (p : Ω)`, then a primitive `p`-th root `ζ` from
`HasEnoughRootsOfUnity.exists_primitiveRoot`. Mathlib provides the needed
`HasEnoughRootsOfUnity` instance for separably closed fields. The theorem
then returns `LinearEquiv.ofBijective (toIntegral hζ)`, using the
injectivity and surjectivity above.
