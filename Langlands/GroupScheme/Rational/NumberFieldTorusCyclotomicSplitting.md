# Torsion torus cocycles over number fields split in cyclotomic extensions

Module: `Langlands.GroupScheme.Rational.NumberFieldTorusCyclotomicSplitting`.

The module states one proposition, `NumberFieldTorusCocycleCyclotomicSplittingStatement`,
and does not prove it.

## The statement

```lean
∀ (K : Type u) [Field K] [NumberField K]
  (T : CommGroupScheme (Spec (CommRingCat.of K))), IsTorus T.toGrp →
  ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (τ : Cocycle T.toGrp (GaloisCocycle.cover K L)) (m : ℕ), 0 < m →
    (τ.map (CommGroupScheme.groupHom (m • 𝟙 T))).IsTrivial →
    ∃ N : ℕ, 0 < N ∧ (∀ q : ℕ, q.Prime → q ∣ N → q ∣ m) ∧
      ∀ (E : Type u) [Field E] [Algebra K E] (ζ : E), IsPrimitiveRoot ζ N →
        (τ.baseChangePullback (algebraBaseMap K E)).IsTrivial
```

Let `K` be a number field and `T` a torus over `K`, given as a commutative group scheme
over `Spec K` satisfying the Library's `IsTorus` (it becomes a split torus over some
field extension). Let `L/K` be a finite Galois extension and `τ` a cocycle of `T` on the
cover `Spec L → Spec K` (module `TorsorCocycle`; `GaloisCocycle.cover K L` is `Spec L`
as a scheme over `Spec K`). Suppose the `m`-th power of `τ` is trivial for some `m > 0`.
Then there is a positive integer `N`, each of whose prime factors divides `m`, such that
`τ` becomes trivial after base change to every field `E` over `K` containing a primitive
`N`-th root of unity.

Conventions:

- The Hom groups of `CommGroupScheme` are written additively, the sum of two
  homomorphisms being their pointwise product. Hence `m • 𝟙 T` is the endomorphism
  `t ↦ t^m` of `T`, and `τ.map (CommGroupScheme.groupHom (m • 𝟙 T))` is the cocycle whose
  values are the `m`-th powers of the values of `τ`. In terms of Galois cohomology, its
  triviality says that the class of `τ` in `H¹(L/K, T(L))` is killed by `m`.
- `Cocycle.IsTrivial` says that a cocycle is the coboundary of one point of the group over
  the cover.
- `algebraBaseMap K E` is `Spec E → Spec K`, and `τ.baseChangePullback (algebraBaseMap K E)`
  (module `CocycleBaseChangeTriviality`) is the cocycle of the base-changed torus `T_E`
  on the pulled-back cover `Spec (L ⊗_K E) → Spec E`. Its triviality says that the class
  of `τ` restricts to the trivial class over `E`.
- The field `E` is arbitrary (not necessarily finite or algebraic over `K`); the
  condition on `E` is the existence of an element `ζ` with `IsPrimitiveRoot ζ N`, so that
  `E` contains a copy of the cyclotomic field `K(ζ_N)` over `K`.

If `τ` is already trivial one may take `N = 1`, for which every field qualifies.

## Source

V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory* (1994), registered as
`platonov-rapinchuk-1994-algebraic-groups-number-theory` (printed page `p` is PDF page
`p + 10`), §6.5, printed pp. 340–341:

- Proposition 6.20: for a number field `K` and a set of primes `Π`, let `K_Π` be the field
  obtained by adjoining to `K` all roots of unity whose orders have only prime factors in
  `Π`. Then `cd_p(K_Π) ≤ 1` for every `p ∈ Π`. The book refers to the proof of
  Proposition 9 of Serre's *Cohomologie galoisienne*.
- Lemma 6.20: if `cd_p(K) ≤ 1`, then `H¹(K, T)` has no `p`-torsion for every `K`-torus
  `T`.

J.-P. Serre, *Galois Cohomology* (corrected second printing 2002), registered as
`serre-1997-galois-cohomology`, Chapter II, §3.3(d), Proposition 9, printed p. 81: an
algebraic extension `k` of `ℚ` has `cd_p(k) ≤ 1` when the exponent of `p` in every
nonarchimedean local degree of `k` is infinite and either `p ≠ 2` or `k` is totally
imaginary. The field `K_Π` satisfies these conditions for `p ∈ Π`: at every finite place
the adjunction of all `p`-power roots of unity has local degree divisible by `p^∞`, and if
`2 ∈ Π` the field contains `√−1`.

## Derivation of the statement

The Lean statement is the consequence of these results that the Hasse-principle arguments
of Platonov–Rapinchuk §6.8 use (printed pp. 377–378, after the Corollary to
Proposition 6.21): a torsion class in `H¹(K, T)` dies over a finite cyclotomic extension.
Let `Π` be the set of prime divisors of `m`. The class of `τ` in `H¹(K, T)` is killed by
`m`, so by Proposition 6.20 and Lemma 6.20 its restriction to `K_Π` is trivial. Since
`K_Π` is the union of the fields `K(ζ_N)` for `N` with prime factors in `Π`, and Galois
cohomology of a torus commutes with this direct limit, the class is already trivial over
some `K(ζ_N)`. Every field `E` over `K` with a primitive `N`-th root of unity contains a
`K`-embedded copy of `K(ζ_N)`, so the class is trivial over `E`. A proof of the Lean
statement also has to compare the Library's cocycles on finite Galois field covers, their
base changes and their triviality with these Galois-cohomological notions.
