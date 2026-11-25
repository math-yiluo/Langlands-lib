# The base case: the trace is an isomorphism

`Langlands/GaloisCohomology/Global/PoitouTate/BaseCase/Trace.lean`, namespace `Langlands.GaloisCohomology.PoitouTate.Internal`.

For `n = ℓᵏ` a prime power, `S` finite containing the places above `ℓ`, `n` odd or `K` totally complex,
the trace `finiteTrace : H_c³(G_S, μ_n) → ℤ/n` is bijective (`bijective_finiteTrace`). It is onto
because the local invariants are (`surjective_finiteTrace`). It is injective because a family of
classes `ξ_v ∈ H²(K_v, μ_n)`, `v ∈ S`, with sum of invariants zero comes from `H²(G_S, μ_n)`: the
Brauer classes of the `ξ_v` (injective images, by Hilbert 90 and the local Kummer sequence,
`injective_coeffMap_rootsOfUnityLocalHom_two`) are the localizations of a class of
`H²(G_S, 𝒪_{K_S,S}ˣ)` killed by `n` (`existsUnique_maximalSUnitsInflation_localization`), which comes
from `H²(G_S, μ_n)` by the Kummer sequence of the `S`-units (`sUnitsKummerSequence_shortExact`).

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.PoitouTate.Internal.bijective_finiteTrace.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (n : ℕ) [NeZero n] [Finite ↑S] {ℓ k : ℕ}
  (hℓ : Nat.Prime ℓ) (hk : k ≠ 0) (hnk : n = ℓ ^ k)
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S)
  (hK : Odd n ∨ NumberField.IsTotallyComplex K) :
  Function.Bijective ⇑(Langlands.GaloisCohomology.PoitouTate.finiteTrace ι S n hK)
Langlands.GaloisCohomology.PoitouTate.Internal.injective_coeffMap_rootsOfUnityLocalHom_two.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (n : ℕ) [NeZero n]
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
  Function.Injective
    ⇑(ModuleCat.Hom.hom
        (Langlands.ProfiniteCohomology.coeffMap (Langlands.GaloisCohomology.PoitouTate.rootsOfUnityLocalHom ι S n v) 2))
Langlands.GaloisCohomology.PoitouTate.Internal.injective_finiteTrace.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (n : ℕ) [NeZero n] [Finite ↑S] {ℓ k : ℕ}
  (hℓ : Nat.Prime ℓ) (hk : k ≠ 0) (hnk : n = ℓ ^ k)
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S)
  (hK : Odd n ∨ NumberField.IsTotallyComplex K) :
  Function.Injective ⇑(Langlands.GaloisCohomology.PoitouTate.finiteTrace ι S n hK)
```

## Outline of the proofs

Injectivity: write `z` as the image of local classes `ξ_v` with sum of invariants `0`; their Brauer classes are the localizations of an `ℓ`-primary class `y ∈ H²(G_S, 𝒪_{K_S,S}ˣ)` (`existsUnique_maximalSUnitsInflation_localization` of the Library), killed by `n` by uniqueness; the Kummer sequence of the `S`-units (`sUnitsKummerSequence_shortExact`) lifts `y` to `x ∈ H²(G_S, μ_n)`, whose localizations are the `ξ_v` since `H²(K_v, μ_n) → Br(K_v)` is injective (Hilbert 90, `subsingleton_cohomology_one_unitsModule`); so `z = 0`. Surjectivity: `surjective_finiteTrace`.

## Declarations

`injective_coeffMap_rootsOfUnityLocalHom_two`, `injective_finiteTrace`, `bijective_finiteTrace`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008, corrected printing 2013), chapter VIII, §6: Theorem (8.6.7) (Poitou–Tate duality), p. 485; Proposition (8.6.8) (the pairing through cup products), p. 487; (8.6.10) (the long exact sequence of Poitou–Tate, and the real places in degrees `≥ 3`), pp. 489–490.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter I, §4, Theorem 4.10, pp. 56–57; chapter II, §2, pp. 165–166 (cohomology with compact support).
