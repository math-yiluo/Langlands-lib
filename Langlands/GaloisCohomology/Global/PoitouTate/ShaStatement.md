# The duality of Tate–Shafarevich groups for `G_S`: statement

`Langlands/GaloisCohomology/Global/PoitouTate/ShaStatement.lean`, namespace `Langlands.GaloisCohomology`.

For a number field `K`, a separable closure `Ω`, a finite set `S` of finite places containing the
places above `N ≥ 1`, `G_S = Gal(K_S/K)` and a finite smooth `G_S`-module `M` killed by `N` with dual
`M' = Hom(M, μ_N)`, the groups `Ш¹_S(M)` and `Ш²_S(M')` of classes vanishing at the places of `S` and
at the real places (`sha`) are finite, and the pairing `Ш¹_S(M) × Ш²_S(M') → ℚ/ℤ`
(`PoitouTate.shaPairing`) is perfect. `PoitouTate.IsShaDuality ι N M` collects these four facts and
`PoitouTateShaStatement` asserts them for all `K`, `Ω`, `S`, `ι`, `N` and `M`. It is proved in
`Langlands.GaloisCohomology.Global.PoitouTate.ShaProof`.

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.PoitouTate.IsShaDuality.bijective_shaPairing.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} [Langlands.IsSmoothRep M]
  [Finite ↑M] (self : Langlands.GaloisCohomology.PoitouTate.IsShaDuality ι N M) :
  Function.Bijective ⇑(Langlands.GaloisCohomology.PoitouTate.shaPairing ι N M)
Langlands.GaloisCohomology.PoitouTate.IsShaDuality.bijective_shaPairing_flip.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} [Langlands.IsSmoothRep M]
  [Finite ↑M] (self : Langlands.GaloisCohomology.PoitouTate.IsShaDuality ι N M) :
  Function.Bijective ⇑(Langlands.GaloisCohomology.PoitouTate.shaPairing ι N M).flip
Langlands.GaloisCohomology.PoitouTate.IsShaDuality.finite_sha_one.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  [Finite ↑S] {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} [Langlands.IsSmoothRep M]
  [Finite ↑M] (self : Langlands.GaloisCohomology.PoitouTate.IsShaDuality ι N M) :
  Finite ↥(Langlands.GaloisCohomology.sha ι M 1)
Langlands.GaloisCohomology.PoitouTate.IsShaDuality.finite_sha_two.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  [Finite ↑S] {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} [Langlands.IsSmoothRep M]
  [Finite ↑M] (self : Langlands.GaloisCohomology.PoitouTate.IsShaDuality ι N M) :
  Finite ↥(Langlands.GaloisCohomology.sha ι (Langlands.GaloisCohomology.PoitouTate.dual N M) 2)
Langlands.GaloisCohomology.PoitouTate.IsShaDuality.mk.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  [Finite ↑S] {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} [Langlands.IsSmoothRep M]
  [Finite ↑M] (finite_sha_one : Finite ↥(Langlands.GaloisCohomology.sha ι M 1))
  (finite_sha_two : Finite ↥(Langlands.GaloisCohomology.sha ι (Langlands.GaloisCohomology.PoitouTate.dual N M) 2))
  (bijective_shaPairing : Function.Bijective ⇑(Langlands.GaloisCohomology.PoitouTate.shaPairing ι N M))
  (bijective_shaPairing_flip : Function.Bijective ⇑(Langlands.GaloisCohomology.PoitouTate.shaPairing ι N M).flip) :
  Langlands.GaloisCohomology.PoitouTate.IsShaDuality ι N M
Langlands.GaloisCohomology.PoitouTate.IsShaDuality.rec.{u_1, u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  [Finite ↑S] {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} [Langlands.IsSmoothRep M]
  [Finite ↑M] {motive : Langlands.GaloisCohomology.PoitouTate.IsShaDuality ι N M → Sort u_1}
  (mk :
    (finite_sha_one : Finite ↥(Langlands.GaloisCohomology.sha ι M 1)) →
      (finite_sha_two : Finite ↥(Langlands.GaloisCohomology.sha ι (Langlands.GaloisCohomology.PoitouTate.dual N M) 2)) →
        (bijective_shaPairing : Function.Bijective ⇑(Langlands.GaloisCohomology.PoitouTate.shaPairing ι N M)) →
          (bijective_shaPairing_flip :
              Function.Bijective ⇑(Langlands.GaloisCohomology.PoitouTate.shaPairing ι N M).flip) →
            motive ⋯)
  (t : Langlands.GaloisCohomology.PoitouTate.IsShaDuality ι N M) : motive t
Langlands.GaloisCohomology.PoitouTate.IsShaDuality.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ) [NeZero N]
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] : Prop
Langlands.GaloisCohomology.PoitouTateShaStatement.{u} : Prop
```

## Outline of the proofs

Statement only.

## Declarations

`IsShaDuality`, `PoitouTateShaStatement`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008, corrected printing 2013), chapter VIII, §6: Theorem (8.6.7) (Poitou–Tate duality), p. 485; Proposition (8.6.8) (the pairing through cup products), p. 487; (8.6.10) (the long exact sequence of Poitou–Tate, and the real places in degrees `≥ 3`), pp. 489–490.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter I, §4, Theorem 4.10, pp. 56–57; chapter II, §2, pp. 165–166 (cohomology with compact support).
