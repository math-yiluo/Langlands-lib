# Proof of solvability of actual finite p-adic inertia groups

Author: Worker 231.

The closing theorem `Langlands.Ramification.Padic.finiteInertiaSolvability` has type
`Langlands.Ramification.Padic.FiniteInertiaSolvability.{u, v}`. This is the proposition
published in `Langlands.LocalFactor.Ramification.InertiaSolvabilityStatement`, with
independent universes `u` and `v`. Thus, for every prime `p`, every
`K : PadicField.{u} p`, every `L : PadicField.{v} p` and the instances
`[Algebra K.Carrier L.Carrier]`, `[IsScalarTower (Padic p) K.Carrier L.Carrier]` and
`[IsGalois K.Carrier L.Carrier]`, it proves

```lean
Group.IsSolvable
  (Langlands.Ramification.Padic.inertia L.canonicalTopologicalData K.Carrier)
```

The proof adds no hypotheses, and the statement pair and its imports are unchanged.
Besides the statement, the module imports the published modules
`Langlands.Galois.Local.TotallyRamifiedSolvabilityProof` and
`Langlands.LocalField.Normalization.Proof`. The `IsGalois` instance is never used. No
total ramification, fixed residue representatives, tame cyclicity, wild `p`-group or
quotient structure is assumed anywhere. The closing theorem depends only on the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Strategy

Write `G` for `L.Carrier ≃ₐ[K.Carrier] L.Carrier` and `O`, `m`, `k` for the integer ring,
maximal ideal and residue field of `T = L.canonicalTopologicalData`. Write `G_i` for the
Library's `Langlands.Ramification.lowerGroup O G i`, formed with the published action
`Padic.integerAction T K.Carrier`. This is the group of elements `g` with
`g • x - x ∈ m ^ (i + 1)` for all `x : O`. The published `Padic.lowerRamificationGroup`
is by definition this group, and `Padic.lowerRamificationGroup_zero` identifies `G_0`
with the actual inertia kernel `Padic.inertia T K.Carrier`.

1. **`G_0 / G_1` is abelian.** The published uniformizer character sends `g ∈ G_0` to
   the residue of `g • ϖ / ϖ` in `k`. Since `k` is commutative, it sends every
   commutator to `1`, so a commutator `c` satisfies `c • ϖ - ϖ ∈ m ^ 2`. Every element
   of `G_0` moves `p`-th powers by elements of `m ^ 2`. An element of `G_0` that moves
   `ϖ` by an element of `m ^ 2` also moves every element of `m` by an element of
   `m ^ 2`. Frobenius is surjective on the finite field `k`, so every `x : O` is a
   `p`-th power plus an element of `m`. Hence `c ∈ G_1`.
2. **The derived series lies in the filtration.** The published bound
   `⁅G_i, G_i⁆ ≤ G_{i+1}` for `i ≥ 1` and step 1 show by induction that the `n`th
   derived subgroup of `G_0` lies in `G_n`.
3. **Termination.** The published `Padic.exists_lowerRamificationGroup_eq_bot` gives
   `G_b = ⊥` for some `b`. Then the `b`th derived subgroup of `G_0` is trivial, so
   `G_0` is solvable.

## Correspondence with the original source

The source is Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
Graduate Texts in Mathematics 67, Springer, 1979 (registered source
`serre-1979-local-fields`). Chapter IV, §2, Corollary 5, printed p.68 (PDF p.75),
asserts that `G_0` is solvable. Serre deduces it from Corollaries 1 and 3 of
Proposition 7, printed p.67 (PDF p.74). These say that `G_0 / G_1` is cyclic and that
`G_1` is a `p`-group, so `G_0` is an extension of solvable groups. Proposition 7 embeds
`G_i / G_{i+1}` into `U_L^{(i)} / U_L^{(i+1)}` through `s ↦ s(π) / π`. The proof of
Proposition 5, printed p.66 (PDF p.73), first reduces to the totally ramified case by
replacing `G` with `G_0` and `K` with the fixed field of `G_0`.

The Lean proof follows a different route. It does not show that `G_0 / G_1` is cyclic
or that `G_1` is a `p`-group, and it does not pass to the fixed field of `G_0`. Step 1
replaces the uniformizer test of Proposition 5 for `i = 1` by the Frobenius argument
above. That argument needs only the published uniformizer character and a perfect
residue field of characteristic `p`. Step 2 uses the published consequence
`⁅G_i, G_i⁆ ≤ G_{i+1}` (`i ≥ 1`) of the commutator bound `⁅G_i, G_i⁆ ≤ G_{2i}`. This
yields the derived-series bound without describing the quotients.

## Generic lemmas over a local ring

Section `Frobenius` in namespace `Langlands.Ramification` works with a commutative
local ring `R`, a group `G` acting on it by `[MulSemiringAction G R]`, and an element
`ϖ` with `hϖ : maximalIdeal R = Ideal.span {ϖ}`. Write `m = maximalIdeal R`. The
Library's `congruenceGroup R G n` consists of the `g` with `g • x - x ∈ m ^ n` for all
`x`. By definition, `lowerGroup R G i` is `congruenceGroup R G (i + 1)`.

- `smul_sub_mem_sq_of_mem_maximalIdeal hϖ`: if `g ∈ lowerGroup R G 0`,
  `g • ϖ - ϖ ∈ m ^ 2` and `b ∈ m`, then `g • b - b ∈ m ^ 2`. Write `b = c * ϖ`.
  Then

  ```text
  g • (c * ϖ) - c * ϖ = (g • c) * (g • ϖ - ϖ) + (g • c - c) * ϖ.
  ```

  The first term lies in `m ^ 2`, and the second lies in `m * m` because
  `g • c - c ∈ m`.
- `smul_pow_sub_mem_sq`: if `p` is prime, `(p : R) ∈ m` and `g ∈ lowerGroup R G 0`,
  then `g • y ^ p - y ^ p ∈ m ^ 2` for every `y : R`. Put `d = g • y - y ∈ m`.
  Mathlib's `exists_add_pow_prime_eq` gives `r` with
  `(y + d) ^ p = y ^ p + d ^ p + p * y * d * r`. Since `y + d = g • y`, this gives

  ```text
  g • y ^ p - y ^ p = d ^ p + (p * d) * (y * r).
  ```

  Here `d ^ p ∈ m ^ p ⊆ m ^ 2`, because `p ≥ 2`, and `p * d ∈ m * m`.
- `mem_lowerGroup_one_of_frobenius hϖ`: assume `p` is prime, `(p : R) ∈ m` and

  ```lean
  hfrob : ∀ x : R, ∃ y : R, x - y ^ p ∈ maximalIdeal R
  ```

  If `g ∈ lowerGroup R G 0` and `g • ϖ - ϖ ∈ m ^ 2`, then `g ∈ lowerGroup R G 1`. For
  `x : R`, choose `y` from `hfrob` and put `b = x - y ^ p ∈ m`. Then
  `g • x - x = (g • y ^ p - y ^ p) + (g • b - b)`, and the two previous lemmas put
  both terms in `m ^ 2`.

The remaining lemmas also assume `[IsDomain R]`, `hϖ0 : ϖ ≠ 0`, the primality of `p`,
`(p : R) ∈ m` and `hfrob`.

- `commutator_lowerGroup_zero_le_of_frobenius`:
  `⁅lowerGroup R G 0, lowerGroup R G 0⁆ ≤ lowerGroup R G 1`. By
  `Subgroup.commutator_le` it suffices to treat `⁅g, h⁆` with `g, h ∈ G_0`. The
  published `uniformizerCharacter hϖ hϖ0 : lowerGroup R G 0 →* ResidueField R` sends
  the commutator of `g` and `h` in `G_0` to `1`. In Lean this goes through
  `MonoidHom.toHomUnits`, whose target is the commutative unit group of the residue
  field, together with `map_commutatorElement` and
  `commutatorElement_eq_one_iff_mul_comm`. The published
  `smul_uniformizer_sub_mem_of_eq_one` then gives `⁅g, h⁆ • ϖ - ϖ ∈ m ^ 2`, and
  `mem_lowerGroup_one_of_frobenius` concludes.
- `map_derivedSeries_lowerGroup_zero_le n`: the image of `derivedSeries (G_0) n` under
  the inclusion `G_0 → G` lies in `lowerGroup R G n`. The proof is by induction on
  `n`. For `n = 0` the image of `⊤` is the range of the inclusion, which is `G_0`. In
  the successor step, `derivedSeries_succ` and `Subgroup.map_commutator` turn the
  image into a commutator of images, and `Subgroup.commutator_mono` bounds it by
  `⁅G_n, G_n⁆`. This lies in `G_{n+1}` by the previous lemma when `n = 0` and by the
  published `commutator_lowerGroup_le_succ` when `n ≥ 1`.
- `isSolvable_lowerGroup_zero_of_frobenius`: if `lowerGroup R G b = ⊥` for some `b`,
  then `Group.IsSolvable (lowerGroup R G 0)`. The previous lemma puts the image of
  `derivedSeries (G_0) b` in `⊥`. Because the inclusion is injective
  (`Subgroup.map_eq_bot_iff_of_injective`), `derivedSeries (G_0) b = ⊥`.

## The p-adic case

Namespace `Langlands.Ramification.Padic` uses the variables of the published module
`Langlands.LocalFactor.Ramification.Galois`: a prime `p` with `[Fact p.Prime]`,
`F : PadicField.{uL} p`, `T : F.TopologicalData` and a field `K : Type uK` with
`[Algebra (Padic p) K]`, `[Algebra K F.Carrier]` and
`[IsScalarTower (Padic p) K F.Carrier]`.

- `isSolvable_inertia T K`: `Group.IsSolvable (inertia T K)`. The proof installs the
  published action `integerAction T K` locally. After installing the topology,
  valuative relation and local-field instances of `T`, Mathlib shows that
  `T.Integers` is a discrete valuation ring. An irreducible `ϖ` from
  `IsDiscreteValuationRing.exists_irreducible` satisfies
  `maximalIdeal = Ideal.span {ϖ}` (`Irreducible.maximalIdeal_eq`) and `ϖ ≠ 0`. The
  published instance `T.residueCharP` makes the residue field have characteristic
  `p`, so the residue of `(p : T.Integers)` vanishes and `(p : T.Integers) ∈ m`. The
  published `T.finite_residueField` makes the residue field finite, so Mathlib's
  `surjective_frobenius` applies. Lifting a `p`-th root of the residue of `x` through
  `IsLocalRing.residue_surjective` gives `hfrob`. The published
  `exists_lowerRamificationGroup_eq_bot T K` provides `b` with
  `lowerRamificationGroup T K b = ⊥`. Rewriting the goal with
  `lowerRamificationGroup_zero`, the result follows from
  `isSolvable_lowerGroup_zero_of_frobenius`, because `lowerRamificationGroup T K i`
  is by definition `lowerGroup` for `integerAction T K`.
- `finiteInertiaSolvability`: introduce `p`, `K`, `L` and the instances, and apply
  `isSolvable_inertia` with `T = L.canonicalTopologicalData` and `K.Carrier` as the
  base field.
