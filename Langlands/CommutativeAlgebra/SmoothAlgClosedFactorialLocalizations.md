# Factorial prime localizations of smooth algebras over algebraically closed fields

This helper module reduces factoriality of the prime localizations of a
smooth algebra over an algebraically closed field to two inputs, passed as
explicit hypotheses:

- `hcompl`, the completion identification. For a Noetherian local
  `K`-algebra `R` that is formally smooth over `K` and whose residue field
  is reached by `K` (`algebraMap K (ResidueField R)` surjective), there is
  `n` and a ring isomorphism
  `AdicCompletion (maximalIdeal R) R ≃+* MvPowerSeries (Fin n) K`.
- `hps`, factoriality of power series rings: every
  `MvPowerSeries (Fin n) K` is a `UniqueFactorizationMonoid`.

Both hypotheses concern the fixed field `K : Type u`, and `hcompl`
quantifies over rings `R : Type u`. The module proves no instance of
either hypothesis; the proof of the target theorem supplies them.

```lean
theorem Langlands.CommutativeAlgebra.uniqueFactorizationMonoid_of_adicCompletion
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [UniqueFactorizationMonoid (AdicCompletion (maximalIdeal R) R)] :
    UniqueFactorizationMonoid R

theorem Langlands.CommutativeAlgebra.surjective_algebraMap_residueField_of_isAlgClosed
    (K A : Type*) [Field K] [IsAlgClosed K] [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] (m : Ideal A) [m.IsMaximal] :
    Function.Surjective (algebraMap K (ResidueField (Localization.AtPrime m)))

theorem Langlands.CommutativeAlgebra.uniqueFactorizationMonoid_localization_maximal_of_smooth
    {K : Type u} [Field K] [IsAlgClosed K] {A : Type u} [CommRing A] [Algebra K A]
    [Algebra.Smooth K A]
    (hcompl : ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
      [Algebra K R] [Algebra.FormallySmooth K R],
      Function.Surjective (algebraMap K (ResidueField R)) →
        ∃ n : ℕ, Nonempty (AdicCompletion (maximalIdeal R) R ≃+* MvPowerSeries (Fin n) K))
    (hps : ∀ n : ℕ, UniqueFactorizationMonoid (MvPowerSeries (Fin n) K))
    (m : Ideal A) [m.IsMaximal] : UniqueFactorizationMonoid (Localization.AtPrime m)

theorem Langlands.CommutativeAlgebra.uniqueFactorizationMonoid_localization_of_smooth
    {K : Type u} [Field K] [IsAlgClosed K] {A : Type u} [CommRing A] [Algebra K A]
    [Algebra.Smooth K A]
    (hcompl : ...) (hps : ...)   -- the same two hypotheses
    (P : Ideal A) [P.IsPrime] : UniqueFactorizationMonoid (Localization.AtPrime P)
```

## Completion

`uniqueFactorizationMonoid_of_adicCompletion` applies
`uniqueFactorizationMonoid_of_flat_of_isLocalHom` from
`Langlands.CommutativeAlgebra.FlatLocalFactorialDescent` to the completion
map `R → AdicCompletion (maximalIdeal R) R`. For a Noetherian local ring,
Mathlib provides the instances needed. The completion is flat
(`AdicCompletion.flat_of_isNoetherian`), it is a local ring, and the
completion map is a local homomorphism
(`Mathlib/RingTheory/AdicCompletion/LocalRing.lean`).

## Residue fields at closed points

`surjective_algebraMap_residueField_of_isAlgClosed` uses the fact that the
residue field `m.ResidueField` of `Localization.AtPrime m` is a finite
`A`-module (Mathlib instance for maximal `m`). It is therefore of finite
type over `K` (`Algebra.FiniteType.trans`). By Zariski's lemma
(`finite_of_finite_type_of_isJacobsonRing`, a field is Jacobson) it is a
finite field extension of `K`. Since `K` is algebraically closed,
`IsAlgClosed.algebraMap_bijective_of_isIntegral` makes `K → m.ResidueField`
bijective.

## Closed points

For a maximal ideal `m`, `R := Localization.AtPrime m` is a local ring. It
is Noetherian: `A` is of finite type over a field
(`Algebra.FiniteType.isNoetherianRing`), and localizations of Noetherian
rings are Noetherian. It is formally smooth over `K` through Mathlib's
instance for localizations of formally smooth algebras. The previous
lemma gives the residue-field hypothesis. Then `hcompl` gives a ring
isomorphism from the completion of `R` to some `MvPowerSeries (Fin n) K`.
Factoriality transfers back along it (`MulEquiv.uniqueFactorizationMonoid`
with `hps n`), and the completion lemma makes `R` factorial.

## All points

For a prime `P`, choose a maximal ideal `m ⊇ P` (`Ideal.exists_le_maximal`).
`P` is disjoint from `m.primeCompl`, so its extension `P'` to
`Localization.AtPrime m` is prime, and `P'` contracts to `P`
(`IsLocalization.isPrime_of_isPrime_disjoint`,
`IsLocalization.under_map_of_isPrime_disjoint`). By
`IsLocalization.isLocalization_isLocalization_atPrime_isLocalization`, the
localization of `Localization.AtPrime m` at `P'` is a localization of `A`
at the complement of the contraction, which is `P.primeCompl`. The ring
`Localization.AtPrime P'` is a localization of the factorial ring
`Localization.AtPrime m`, so it is factorial by Mathlib's instance for
localizations of unique factorization monoids. The canonical
`IsLocalization.algEquiv` between the two localizations of `A` at
`P.primeCompl` transfers factoriality to `Localization.AtPrime P`.

## Provenance and contributions

This is an internal derivation for the proof of
`Langlands.AlgebraicGeometry.SmoothAlgClosedFactorialStalks`. It follows
the route recorded there: a smooth local ring at a closed point has
completion `K⟦T_1, ..., T_n⟧`, power series rings over a field are UFDs
(Stacks Remark 10.160.9, Tag 032C, with Lemma 15.123.2, Tag 0AG0),
factoriality descends along the faithfully flat completion map, and
localizations of UFDs are UFDs. Worker 254 wrote the Lean proof and this
description.
