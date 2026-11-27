# Raynaud's criterion from the monodromy theorem and the Galois criterion

This module defines a reduction proposition and proves it.

## The proposition

`Langlands.AbelianScheme.RaynaudSemiabelianCriterionReductionStatement` is

`UnipotentInertiaSemiabelianReductionStatement.{u} →
AbelianInertiaQuasiUnipotentStatement.{u} →
RaynaudSemiabelianCriterionStatement.{u}`.

The three propositions are Library statements in `Langlands/AbelianScheme/`.

- `UnipotentInertiaSemiabelianReductionStatement`: let `ℓ` be a prime
  invertible in the valuation ring `V`. Its test rings are the discrete
  valuation rings `W` that are Henselian with separably closed residue
  field, together with a local homomorphism `V → W` under which the maximal
  ideal of `V` generates the maximal ideal of `W`, and a fraction field `L`
  of `W` with a field map `K → L` compatible with `V → W`. If, for every
  such `W` and `L` and every geometric point of `Spec L`, every element of
  the fundamental group of `Spec L` acts unipotently on the rational
  `ℓ`-adic Tate module of the base change of `B` to `L`, then every Néron
  model of `B` has semiabelian geometric special identity component
  (Grothendieck's Galois criterion, SGA 7 I, Exposé IX, 3.5 and 3.8). The
  residue field extension of `V → W` is not required to be separable,
  whereas Bosch, Lütkebohmert and Raynaud, *Néron Models*, §7.2, p. 176,
  include separability of the residue extension in their notion of
  ramification index 1. The strict henselization of `V` is among the test
  rings, which connects the hypothesis with the inertia condition of the
  sources.
- `AbelianInertiaQuasiUnipotentStatement`: let `W` be a Henselian discrete
  valuation ring with separably closed residue field, `L` a fraction field
  of `W`, `A` an abelian variety over `L` and `ℓ` a prime invertible in
  `W`. At every geometric point of `Spec L`, every element of the
  fundamental group of `Spec L` has a positive power acting unipotently on
  the rational `ℓ`-adic Tate module of `A` (Grothendieck's monodromy
  theorem, SGA 7 I, Exposé I, 1.2 and 1.3).
- `RaynaudSemiabelianCriterionStatement`: if `n ≥ 3` is a unit of the
  valuation ring and all `n`-torsion points over an algebraic closure are
  rational, every Néron model has semiabelian geometric special identity
  component.

The theorem `raynaudSemiabelianCriterionReduction` proves the reduction.
The module also proves the arithmetic lemma `exists_prime_pow_dvd_three_le`:
every natural number `n ≥ 3` has a divisor `ℓ ^ a ≥ 3` with `ℓ` prime. If
`n` has an odd prime factor `ℓ`, take `a = 1`. Otherwise `n` is a power of
`2` (`Nat.eq_prime_pow_of_unique_prime_dvd`) with exponent at least `2`,
and `4` divides it.

## Proof

Fix `V`, `K`, `B`, a Néron model `N`, `n ≥ 3` invertible in `V`, and
`HasRationalGeometricTorsion B n`.

1. `exists_prime_pow_dvd_three_le` gives a prime `ℓ` and `a` with
   `ℓ ^ a ∣ n` and `3 ≤ ℓ ^ a`. Then `ℓ ∣ n`, so `ℓ` is a unit of `V`, and
   `n` is a unit of `K`.
2. The Galois criterion, `UnipotentInertiaSemiabelianReductionStatement`,
   is applied to `V`, `K`, `B`, `N` and `ℓ`. It remains to show its
   hypothesis. Fix a test ring `W` with its fraction field `L` as above:
   `W` is a Henselian discrete valuation ring with separably closed residue
   field, `V → W` is a local homomorphism under which the maximal ideal of
   `V` generates the maximal ideal of `W`, and `K → L` is compatible with
   `V → W`. Fix also a geometric point `s : Spec Ω → Spec L`, the
   invertibility witnesses `hu` and an element `g` of the fundamental
   group. Let `A` be the base change of `B` to `L`.
3. `ℓ` is a unit of `W`. So `AbelianInertiaQuasiUnipotentStatement` for
   `W`, `L`, `A` and `ℓ` gives `m > 0` such that `g ^ m` acts unipotently
   on the rational Tate module.
4. Let `σ` be the action of `g` on the integral `ℓ`-adic Tate module
   (`Tate.PrimeAdic.monodromyMap`). By
   `RationalTorsionMonodromy.torsionPointsRational_baseChange` and
   `RationalTorsionMonodromy.monodromyMap_sub_one_valuesDivisible`
   (`Langlands/AbelianScheme/RationalTorsionMonodromy.lean`), every value
   of `σ - 1` is `ℓ ^ a` times an element. This uses the rationality of the
   `n`-torsion and `ℓ ^ a ∣ n`.
5. `RationalTorsionMonodromy.isNilpotent_rationalMonodromy_pow_sub_one_iff`
   turns step 3 into the nilpotence of `σ ^ m - 1` on the integral Tate
   module.
6. The integral Tate module has no `ℓ`-torsion, and no nonzero element is
   divisible by every power of `ℓ`
   (`RationalTorsionMonodromy.integral_eq_zero_of_nsmul_eq_zero` and
   `RationalTorsionMonodromy.integral_eq_zero_of_forall_dvd`). The lemma
   `isNilpotent_sub_one_of_isNilpotent_pow_sub_one` of
   `Langlands/LinearAlgebra/CongruentQuasiUnipotent.lean` then makes
   `σ - 1` nilpotent.
7. `RationalTorsionMonodromy.isNilpotent_rationalMonodromy_sub_one_iff`
   turns this into the unipotence of `g` on the rational Tate module, which
   is the hypothesis of the Galois criterion.

## Provenance

The route is that of Raynaud's criterion, Silverberg and Zarhin,
*Semistable reduction and torsion subgroups of abelian varieties*, Ann.
Inst. Fourier 45 (1995), §3, printed p. 406, Theorem 3.5, with proof
reference SGA 7 I, Exposé IX, Proposition 4.7, arranged so that it does
not use the semistable reduction theorem. SGA 7 IX, 4.1–4.2 and 4.7 obtain
the criterion from the semistable reduction theorem 3.6. Here the inputs
are the monodromy theorem, which gives quasi-unipotence directly, and the
Galois criterion in the form of SGA 7 IX, Corollaire 3.8. In SGA 7 IX, 4.7
the trivial inertia action on the `n`-torsion is applied to the torsion of
the semiabelian special fibre of a model with semistable reduction. The
congruence of the whole integral Tate-module monodromy modulo `ℓ ^ a`
(step 4) is instead derived in
`Langlands/AbelianScheme/RationalTorsionMonodromy.lean` from the naturality
of the action on the finite étale torsion levels. The Minkowski–Serre
step (SGA 7 IX, 4.7.1 and 4.7.3; Silverberg and Zarhin, §4, Theorem 4.1)
is replaced by the lemma on congruent quasi-unipotent endomorphisms of
`Langlands/LinearAlgebra/CongruentQuasiUnipotent.lean`. This module proves
only the implication. It does not prove either input.
