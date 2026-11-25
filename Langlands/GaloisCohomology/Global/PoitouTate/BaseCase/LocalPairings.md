# The base case: the local pairings

`Langlands/GaloisCohomology/Global/PoitouTate/BaseCase/LocalPairings.lean`, namespace `Langlands.GaloisCohomology.PoitouTate.Internal`.

At a finite place `v ∈ S` of a number field `K` containing the `n`-th roots of unity, the pairing
`μ_n ⊗ ℤ/n → μ_n → K̄_vˣ` identifies `ℤ/n` with the Cartier dual of `μ_n` (`zmodToCartier`,
`bijective_zmodToCartier`, `tensorHom_zmodToCartier_cartierPairing`). Local Tate duality for `μ_n`
(`localTateDualityStatement`) then shows that the pairings `Hˢ(K_v, μ_n) × Hʳ(K_v, ℤ/n) → ℤ/n`
(`r + s = 2`), cup product with `μ_n ⊗ ℤ/n → μ_n` followed by the local trace, are perfect in the
second variable (`bijective_localTrace_cupPairing`): these are the local hypotheses of the abstract
base case.

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.PoitouTate.Internal.bijective_localTrace_cupPairing.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (n : ℕ) [NeZero n]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S) {r s : ℕ}
  (h : s + r = 2) :
  Function.Bijective fun ξ =>
    (Langlands.GaloisCohomology.PoitouTate.Internal.localTrace ι S n v).comp
      ((Langlands.ProfiniteCohomology.bilinAddHom
            (Langlands.ProfiniteCohomology.cupPairing
              (Langlands.GaloisCohomology.pairingRes (↑(Langlands.Galois.localizationHom ι S v))
                (Langlands.GaloisCohomology.zmodMulPairingRight n
                  (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S n) ⋯))
              h)).flip
        ξ)
Langlands.GaloisCohomology.PoitouTate.Internal.bijective_zmodToCartier.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (n : ℕ) [NeZero n]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S) :
  Function.Bijective ⇑(Rep.Hom.hom (Langlands.GaloisCohomology.PoitouTate.Internal.zmodToCartier ι S n v))
Langlands.GaloisCohomology.PoitouTate.Internal.tensorHom_zmodToCartier_cartierPairing.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (n : ℕ)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
  CategoryTheory.CategoryStruct.comp
      (CategoryTheory.MonoidalCategoryStruct.tensorHom
        (CategoryTheory.CategoryStruct.id
          (Langlands.GaloisCohomology.localModule ι (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S n) v))
        (Langlands.GaloisCohomology.PoitouTate.Internal.zmodToCartier ι S n v))
      (Langlands.GaloisCohomology.cartierPairing (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
        (Langlands.GaloisCohomology.localModule ι (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S n) v)) =
    CategoryTheory.CategoryStruct.comp
      (Langlands.GaloisCohomology.pairingRes (↑(Langlands.Galois.localizationHom ι S v))
        (Langlands.GaloisCohomology.zmodMulPairingRight n
          (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S n) ⋯))
      (Langlands.GaloisCohomology.PoitouTate.rootsOfUnityLocalHom ι S n v)
Langlands.GaloisCohomology.PoitouTate.Internal.zmodToCartier.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (n : ℕ)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
  Langlands.GaloisCohomology.localModule ι
      (Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n) v ⟶
    Langlands.GaloisCohomology.cartierDual (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
      (Langlands.GaloisCohomology.localModule ι (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S n) v)
Langlands.GaloisCohomology.PoitouTate.Internal.zmodToCartier_hom_apply.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (n : ℕ)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (a : ZMod n)
  (ζ : ↑(Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S n)) :
  ((Rep.Hom.hom (Langlands.GaloisCohomology.PoitouTate.Internal.zmodToCartier ι S n v)) { down := a }) ζ =
    (Rep.Hom.hom (Langlands.GaloisCohomology.PoitouTate.rootsOfUnityLocalHom ι S n v)) (a.cast • ζ)
```

## Outline of the proofs

`zmodToCartier` is the adjoint (`Rep.tensorHomEquiv`) of `μ_n ⊗ ℤ/n → μ_n → K̄_vˣ`, injective since `μ_n → K̄_vˣ` is and bijective by counting (`card_dualRep_le`, `cartierDualIsoHomRootsOfUnityOfNsmul`); the pairing of the base case is the local Tate pairing for `μ_n` after it (`cupPairing_cohomologyMap`, `cohomologyMap_cupPairing`), and local Tate duality in the second variable gives the bijectivity.

## Declarations

`zmodToCartier`, `zmodToCartier_hom_apply`, `tensorHom_zmodToCartier_cartierPairing`, `bijective_zmodToCartier`, `bijective_localTrace_cupPairing`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008, corrected printing 2013), chapter VIII, §6: Theorem (8.6.7) (Poitou–Tate duality), p. 485; Proposition (8.6.8) (the pairing through cup products), p. 487; (8.6.10) (the long exact sequence of Poitou–Tate, and the real places in degrees `≥ 3`), pp. 489–490.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter I, §4, Theorem 4.10, pp. 56–57; chapter II, §2, pp. 165–166 (cohomology with compact support).
