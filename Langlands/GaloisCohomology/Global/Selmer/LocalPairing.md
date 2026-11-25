# The local pairings in degree one

`Langlands/GaloisCohomology/Global/Selmer/LocalPairing.lean`, namespace `Langlands.GaloisCohomology`.

Let `K` be a number field, `Ω` a separable closure, `S` a finite set of finite places of `K`,
`G_S = Gal(K_S/K)`, `ι : PlaceEmbeddings K Ω`, `N ≥ 1`, `M` a finite smooth `G_S`-module and
`M' = Hom(M, μ_N)` (`PoitouTate.dual`). The map `PoitouTate.locDual` of the Poitou–Tate sequence in
degrees `1 + 1` is the sum of the local pairings (of the module
`Langlands.GaloisCohomology.Global.PoitouTate.LocalPairings`, with `locDual_one_apply`)

* `localPairing ι N M v : H¹(K_v, M) × H¹(K_v, M') → ℚ/ℤ` at the places `v ∈ S`, and
* `realLocalPairing ι N M w : H¹(K_w, M) × H¹(K_w, M') → ℚ/ℤ` at the real places `w`,

the cup product with the evaluation `M ⊗ M' → μ_N` followed by the local invariant
(`ptLocalPairing` with `PoitouTate.invariantAt`, resp. `PoitouTate.realInvariantAt`), with the
localizations of global classes of `M'`: `locDual ι N M ξ y = localTermPairing ι N M ξ (loc y)`
(`locDual_one_apply`), `localTermPairing ι N M` being the sum of all local pairings on
`P¹(M) × P¹(M')`, `P¹ = PoitouTate.LocalTerm · 1`.

When `S` contains the places above `N` and `N` kills `M`, `M'` restricted to `Gal(K̄_v/K_v)` is the
Cartier dual `Hom(M, K̄_vˣ)` (`dualIsoCartierDual`; at a real place `realDualIsoCartierDual`), and every
local pairing is perfect: at `v ∈ S` by local Tate duality, at a real place by duality for
`Gal(ℂ/ℝ)`, on both sides (`bijective_localPairing`, `bijective_localPairing_flip`,
`bijective_realLocalPairing`, `bijective_realLocalPairing_flip`); hence so is `localTermPairing`
(`bijective_localTermPairing`, `bijective_localTermPairing_flip`). `P¹(M)` is finite
(`finite_localTerm_one`).

```lean
def dualIsoCartierDual (v : HeightOneSpectrum (𝓞 K)) :
    localModule ι (dual N M) v ≅
      cartierDual (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) (localModule ι M v)
theorem bijective_localPairing (v : S) : Function.Bijective (localPairing ι N M v)
def realDualIsoCartierDual (w : InfinitePlace K) :
    realLocalModule ι (dual N M) w ≅
      cartierDual w.Completion (AlgebraicClosure w.Completion) (realLocalModule ι M w)
theorem bijective_realLocalPairing (w : {w : InfinitePlace K // w.IsReal}) :
    Function.Bijective (realLocalPairing ι N M w)
theorem bijective_localTermPairing : Function.Bijective (localTermPairing ι N M)
theorem bijective_localTermPairing_flip : Function.Bijective (localTermPairing ι N M).flip
```

## Complete types

In the `#check` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.dualIsoCartierDual : {K Ω : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [inst_4 : IsSepClosure K Ω] →
            {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} →
              (ι : Langlands.Galois.PlaceEmbeddings K Ω) →
                (N : ℕ) →
                  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) →
                    [Finite ↑M] →
                      [NeZero N] →
                        (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
                            ↑N ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S) →
                          (∀ (m : ↑M), N • m = 0) →
                            (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) →
                              Langlands.GaloisCohomology.localModule ι (Langlands.GaloisCohomology.PoitouTate.dual N M)
                                  v ≅
                                Langlands.GaloisCohomology.cartierDual
                                  (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
                                  (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
                                  (Langlands.GaloisCohomology.localModule ι M v)
@Langlands.GaloisCohomology.bijective_localPairing : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
  [inst_5 : Langlands.IsSmoothRep M] [inst_6 : Finite ↑M] [NeZero N],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ↑N ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S) →
    (∀ (m : ↑M), N • m = 0) → ∀ (v : ↑S), Function.Bijective ⇑(Langlands.GaloisCohomology.localPairing ι N M v)
@Langlands.GaloisCohomology.bijective_localPairing_flip : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
  [inst_5 : Langlands.IsSmoothRep M] [inst_6 : Finite ↑M] [NeZero N],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ↑N ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S) →
    (∀ (m : ↑M), N • m = 0) →
      ∀ (v : ↑S), Function.Bijective ⇑(AddMonoidHom.flip (Langlands.GaloisCohomology.localPairing ι N M v))
@Langlands.GaloisCohomology.realDualIsoCartierDual : {K Ω : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [inst_4 : IsSepClosure K Ω] →
            {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} →
              (ι : Langlands.Galois.PlaceEmbeddings K Ω) →
                (N : ℕ) →
                  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) →
                    [Finite ↑M] →
                      [NeZero N] →
                        (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
                            ↑N ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S) →
                          (∀ (m : ↑M), N • m = 0) →
                            (w : NumberField.InfinitePlace K) →
                              Langlands.GaloisCohomology.realLocalModule ι
                                  (Langlands.GaloisCohomology.PoitouTate.dual N M) w ≅
                                Langlands.GaloisCohomology.cartierDual (NumberField.InfinitePlace.Completion w)
                                  (AlgebraicClosure (NumberField.InfinitePlace.Completion w))
                                  (Langlands.GaloisCohomology.realLocalModule ι M w)
@Langlands.GaloisCohomology.realLocalPairing_eq_orderTwoDualityPairing : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
  [inst_5 : Langlands.IsSmoothRep M] [inst_6 : Finite ↑M] (w : { w // NumberField.InfinitePlace.IsReal w })
  (ξ : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.realLocalModule ι M ↑w) 1))
  (η :
    ↑(Langlands.ProfiniteCohomology.cohomology
        (Langlands.GaloisCohomology.realLocalModule ι (Langlands.GaloisCohomology.PoitouTate.dual N M) ↑w) 1)),
  ((Langlands.GaloisCohomology.realLocalPairing ι N M w) ξ) η =
    ((Langlands.GaloisCohomology.orderTwoDualityPairing (Langlands.GaloisCohomology.realInvariantQZ ↑w)
          (Langlands.GaloisCohomology.realLocalModule ι M ↑w) ⋯)
        ξ)
      ((ModuleCat.Hom.hom
          (Langlands.ProfiniteCohomology.coeffMap
            (Langlands.GaloisCohomology.PoitouTate.dualToCartier (Langlands.Galois.realLocalizationHom ι S ↑w)
              (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N)
              (Langlands.GaloisCohomology.PoitouTate.rootsOfUnityRealHom ι S N ↑w) M)
            1))
        η)
@Langlands.GaloisCohomology.bijective_realLocalPairing : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
  [inst_5 : Langlands.IsSmoothRep M] [inst_6 : Finite ↑M] [NeZero N],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ↑N ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S) →
    (∀ (m : ↑M), N • m = 0) →
      ∀ (w : { w // NumberField.InfinitePlace.IsReal w }),
        Function.Bijective ⇑(Langlands.GaloisCohomology.realLocalPairing ι N M w)
@Langlands.GaloisCohomology.bijective_realLocalPairing_flip : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
  [inst_5 : Langlands.IsSmoothRep M] [inst_6 : Finite ↑M] [NeZero N],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ↑N ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S) →
    (∀ (m : ↑M), N • m = 0) →
      ∀ (w : { w // NumberField.InfinitePlace.IsReal w }),
        Function.Bijective ⇑(AddMonoidHom.flip (Langlands.GaloisCohomology.realLocalPairing ι N M w))
@Langlands.GaloisCohomology.finite_localTerm_one : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
  [inst_5 : Langlands.IsSmoothRep M] [Finite ↑M] [Finite ↑S],
  Finite (Langlands.GaloisCohomology.PoitouTate.LocalTerm ι M 1)
@Langlands.GaloisCohomology.bijective_localTermPairing : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
  [inst_5 : Langlands.IsSmoothRep M] [inst_6 : Finite ↑M] [NeZero N],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ↑N ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S) →
    (∀ (m : ↑M), N • m = 0) →
      ∀ [inst_8 : Finite ↑S], Function.Bijective ⇑(Langlands.GaloisCohomology.localTermPairing ι N M)
@Langlands.GaloisCohomology.bijective_localTermPairing_flip : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
  [inst_5 : Langlands.IsSmoothRep M] [inst_6 : Finite ↑M] [NeZero N],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ↑N ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S) →
    (∀ (m : ↑M), N • m = 0) →
      ∀ [inst_8 : Finite ↑S],
        Function.Bijective ⇑(AddMonoidHom.flip (Langlands.GaloisCohomology.localTermPairing ι N M))
```

## Outline of the proofs

- `locDual_one_apply`: `locDual_apply` of `Langlands.GaloisCohomology.Global.PoitouTate.Sequence`
  and the definitions.
- At `v ∈ S`: `PoitouTate.ptLocalPairing_eq_localTatePairing` writes the local pairing as the local
  Tate pairing `localTatePairing` after `dualToCartier`, which is bijective
  (`PoitouTate.bijective_dualToCartier`: `μ_N(K_S) → K̄_vˣ` is injective and both groups of `N`-th
  roots of unity are cyclic of order `N`, `PoitouTate.nonempty_addEquiv_dualizingModule`); local
  Tate duality is `PoitouTate.localTateDualityStatement` (from
  `Langlands.GaloisCohomology.Local.tatePairing_bijective` and `tatePairing_flip_bijective`), and
  perfectness is transported by `bijective_of_pairing_eq_addEquiv`.
- At a real place: `cupPairing_dualToCartier` writes the local pairing as
  `orderTwoDualityPairing (realInvariantQZ w)` after `dualToCartier`, and `realLocalDuality` gives
  perfectness in degrees `1 + 1`.
- On `P¹`: sums of perfect pairings (`bijective_prodPairing`, `bijective_piPairing`).

## Declarations

`dualIsoCartierDual`, `bijective_localPairing`, `bijective_localPairing_flip`, `realDualIsoCartierDual`, `realLocalPairing_eq_orderTwoDualityPairing`, `bijective_realLocalPairing`, `bijective_realLocalPairing_flip`, `finite_localTerm_one`, `bijective_localTermPairing`, `bijective_localTermPairing_flip`.

## References

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed. (Springer 2008, corrected printing 2013), (7.2.6) (Tate duality), p. 380; (7.2.17) (duality for `G(ℂ|ℝ)`), p. 390.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed. (BookSurge 2006), I §4, Theorem 4.10, p. 56 (the local pairings in the sequence of Poitou and Tate).
