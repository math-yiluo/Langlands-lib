# The infinite places of `L` as a `Gal(L/K)`-set

`Langlands/GaloisCohomology/Global/EulerCharacteristic/Internal/InfiniteCount.lean`, namespace `Langlands.GaloisCohomology`.

Let `L ⊆ K_S` be finite Galois over `K` with group `Γ`. For an infinite place `w` of `K`, the place
`w̃_w` of `L` given by the chosen embedding `ι_w` (`infiniteBasePlace`) lies above `w`, and the
infinite places of `L` are `⊔_w Γ/Stab(w̃_w)` as a `Γ`-set (`infinitePlacesEquiv`, from Mathlib's
transitivity of `Γ` on the places above `w`), so that
`d(𝔽_ℓ[∞_L]) = ∑_w d(𝔽_ℓ[Γ/Stab(w̃_w)])` (`toFun_infinitePlaces`). At a complex place the stabilizer
is trivial (`stabilizer_infiniteBasePlace_eq_bot`); at a real place it is `{1, τ_w}` with `τ_w` the
restriction of the complex conjugation at `w` (`mem_stabilizer_infiniteBasePlace_iff`).

```lean
theorem toFun_infinitePlaces {ℓ : ℕ} [NeZero ℓ] (d : AdditiveFunction.{u} ℓ (L ≃ₐ[K] L)) :
    d.toFun (InfinitePlace L → ZMod ℓ) (funPermRep (ZMod ℓ) (L ≃ₐ[K] L) (InfinitePlace L)) =
      ∑ w : InfinitePlace K, d.toFun ((L ≃ₐ[K] L) ⧸ MulAction.stabilizer (L ≃ₐ[K] L)
          (infiniteBasePlace hL ι w) → ZMod ℓ)
        (funPermRep (ZMod ℓ) (L ≃ₐ[K] L) ((L ≃ₐ[K] L) ⧸ MulAction.stabilizer (L ≃ₐ[K] L)
          (infiniteBasePlace hL ι w)))
```

## Complete types

In the `#check @c` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.toFun_infinitePlaces : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {L : Type u} [inst_5 : Field L]
  [inst_6 : NumberField L] [inst_7 : Algebra K L] [inst_8 : Algebra L Ω] [inst_9 : IsScalarTower K L Ω]
  (hL : ∀ (x : L), (algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) [IsGalois K L]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) {ℓ : ℕ} [inst_11 : NeZero ℓ]
  (d : Langlands.GaloisCohomology.Local.AdditiveFunction ℓ Gal(L/K)),
  d.toFun (NumberField.InfinitePlace L → ZMod ℓ)
      (Langlands.GaloisCohomology.funPermRep (ZMod ℓ) Gal(L/K) (NumberField.InfinitePlace L)) =
    ∑ w : NumberField.InfinitePlace K,
      d.toFun (Gal(L/K) ⧸ MulAction.stabilizer Gal(L/K) (Langlands.GaloisCohomology.infiniteBasePlace hL ι w) → ZMod ℓ)
        (Langlands.GaloisCohomology.funPermRep (ZMod ℓ) Gal(L/K)
          (Gal(L/K) ⧸ MulAction.stabilizer Gal(L/K) (Langlands.GaloisCohomology.infiniteBasePlace hL ι w)))
```

## Outline of the proofs

As in `PlaceOrbits` for the infinite places: transitivity of `Gal(L/K)` on the places above `w` (Mathlib's `InfinitePlace.exists_smul_eq_of_comap_eq`), trivial stabilizers at complex places (unramified), and the stabilizer `{1, τ_w}` at a real place, `τ_w` the restriction of complex conjugation.

- `toFun_infinitePlaces`: **The permutation module of the infinite places.** For every additive function `d`: `d(𝔽_ℓ[∞_L]) = ∑_w d(𝔽_ℓ[Gal(L/K)/Stab(w̃_w)])`.

## Declarations

`infiniteBasePlace`, `comap_infiniteBasePlace`, `infinitePlacesFun`, `infinitePlacesFun_mk`, `comap_infinitePlacesFun`, `infinitePlacesEquiv`, `infinitePlacesEquiv_smul`, `toFun_infinitePlaces`, `stabilizer_infiniteBasePlace_eq_bot`, `realConjRestrict`, `isConj_realConjRestrict`, `mem_stabilizer_infiniteBasePlace_iff`.

## References

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed. (Springer 2008, corrected printing 2013), proof of (8.7.4), pp. 506–507 (the terms at S∞(K)).
