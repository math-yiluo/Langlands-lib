# The nine-term sequence of Poitou–Tate for `G_S`: statement

`Langlands/GaloisCohomology/Global/PoitouTate/NineTermStatement.lean`, namespace `Langlands.GaloisCohomology`.

For a number field `K`, a separable closure `Ω`, a finite set `S` of finite places containing the
places above `N ≥ 1`, `G_S = Gal(K_S/K)` and a finite smooth `G_S`-module `M` killed by `N` with dual
`M' = Hom(M, μ_N)`, the sequence

`0 → H⁰(G_S, M) → P̂⁰(M) → H²(G_S, M')^∨ → H¹(G_S, M) → P¹(M) → H¹(G_S, M')^∨ → H²(G_S, M) → P²(M)
  → H⁰(G_S, M')^∨ → 0`

is exact, where `Pⁿ(M) = ∏_{v ∈ S} Hⁿ(K_v, M) × ∏_{w real} Hⁿ(K_w, M)`, `P̂⁰(M)` has Tate's `Ĥ⁰` at
the real places, `X^∨ = Hom(X, ℚ/ℤ)`, and the maps are `PoitouTate.locHat`, `PoitouTate.locDualHat`,
`PoitouTate.connecting`, `PoitouTate.loc`, `PoitouTate.locDual` of
`Langlands.GaloisCohomology.Global.PoitouTate.Sequence`. `PoitouTate.IsNineTermExact ι N M` names the
nine exactness properties and `PoitouTateNineTermStatement` asserts them for all `K`, `Ω`, `S`, `ι`,
`N` and `M`. It is proved in `Langlands.GaloisCohomology.Global.PoitouTate.NineTermProof`.

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.PoitouTate.IsNineTermExact.exact_connecting_loc_one.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} [Langlands.IsSmoothRep M]
  [Finite ↑M] (self : Langlands.GaloisCohomology.PoitouTate.IsNineTermExact ι N M) :
  Function.Exact ⇑(Langlands.GaloisCohomology.PoitouTate.connecting ι N M ⋯)
    ⇑(Langlands.GaloisCohomology.PoitouTate.loc ι M 1)
Langlands.GaloisCohomology.PoitouTate.IsNineTermExact.exact_connecting_loc_two.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} [Langlands.IsSmoothRep M]
  [Finite ↑M] (self : Langlands.GaloisCohomology.PoitouTate.IsNineTermExact ι N M) :
  Function.Exact ⇑(Langlands.GaloisCohomology.PoitouTate.connecting ι N M ⋯)
    ⇑(Langlands.GaloisCohomology.PoitouTate.loc ι M 2)
Langlands.GaloisCohomology.PoitouTate.IsNineTermExact.exact_locDualHat_connecting.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} [Langlands.IsSmoothRep M]
  [Finite ↑M] (self : Langlands.GaloisCohomology.PoitouTate.IsNineTermExact ι N M) :
  Function.Exact ⇑(Langlands.GaloisCohomology.PoitouTate.locDualHat ι N M)
    ⇑(Langlands.GaloisCohomology.PoitouTate.connecting ι N M ⋯)
Langlands.GaloisCohomology.PoitouTate.IsNineTermExact.exact_locDual_connecting_one.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} [Langlands.IsSmoothRep M]
  [Finite ↑M] (self : Langlands.GaloisCohomology.PoitouTate.IsNineTermExact ι N M) :
  Function.Exact ⇑(Langlands.GaloisCohomology.PoitouTate.locDual ι N M ⋯)
    ⇑(Langlands.GaloisCohomology.PoitouTate.connecting ι N M ⋯)
Langlands.GaloisCohomology.PoitouTate.IsNineTermExact.exact_locHat_locDualHat.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} [Langlands.IsSmoothRep M]
  [Finite ↑M] (self : Langlands.GaloisCohomology.PoitouTate.IsNineTermExact ι N M) :
  Function.Exact ⇑(Langlands.GaloisCohomology.PoitouTate.locHat ι M)
    ⇑(Langlands.GaloisCohomology.PoitouTate.locDualHat ι N M)
Langlands.GaloisCohomology.PoitouTate.IsNineTermExact.exact_loc_locDual_one.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} [Langlands.IsSmoothRep M]
  [Finite ↑M] (self : Langlands.GaloisCohomology.PoitouTate.IsNineTermExact ι N M) :
  Function.Exact ⇑(Langlands.GaloisCohomology.PoitouTate.loc ι M 1)
    ⇑(Langlands.GaloisCohomology.PoitouTate.locDual ι N M ⋯)
Langlands.GaloisCohomology.PoitouTate.IsNineTermExact.exact_loc_locDual_two.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} [Langlands.IsSmoothRep M]
  [Finite ↑M] (self : Langlands.GaloisCohomology.PoitouTate.IsNineTermExact ι N M) :
  Function.Exact ⇑(Langlands.GaloisCohomology.PoitouTate.loc ι M 2)
    ⇑(Langlands.GaloisCohomology.PoitouTate.locDual ι N M ⋯)
Langlands.GaloisCohomology.PoitouTate.IsNineTermExact.injective_locHat.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} [Langlands.IsSmoothRep M]
  [Finite ↑M] (self : Langlands.GaloisCohomology.PoitouTate.IsNineTermExact ι N M) :
  Function.Injective ⇑(Langlands.GaloisCohomology.PoitouTate.locHat ι M)
Langlands.GaloisCohomology.PoitouTate.IsNineTermExact.mk.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  [Finite ↑S] {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} [Langlands.IsSmoothRep M]
  [Finite ↑M] (injective_locHat : Function.Injective ⇑(Langlands.GaloisCohomology.PoitouTate.locHat ι M))
  (exact_locHat_locDualHat :
    Function.Exact ⇑(Langlands.GaloisCohomology.PoitouTate.locHat ι M)
      ⇑(Langlands.GaloisCohomology.PoitouTate.locDualHat ι N M))
  (exact_locDualHat_connecting :
    Function.Exact ⇑(Langlands.GaloisCohomology.PoitouTate.locDualHat ι N M)
      ⇑(Langlands.GaloisCohomology.PoitouTate.connecting ι N M ⋯))
  (exact_connecting_loc_one :
    Function.Exact ⇑(Langlands.GaloisCohomology.PoitouTate.connecting ι N M ⋯)
      ⇑(Langlands.GaloisCohomology.PoitouTate.loc ι M 1))
  (exact_loc_locDual_one :
    Function.Exact ⇑(Langlands.GaloisCohomology.PoitouTate.loc ι M 1)
      ⇑(Langlands.GaloisCohomology.PoitouTate.locDual ι N M ⋯))
  (exact_locDual_connecting_one :
    Function.Exact ⇑(Langlands.GaloisCohomology.PoitouTate.locDual ι N M ⋯)
      ⇑(Langlands.GaloisCohomology.PoitouTate.connecting ι N M ⋯))
  (exact_connecting_loc_two :
    Function.Exact ⇑(Langlands.GaloisCohomology.PoitouTate.connecting ι N M ⋯)
      ⇑(Langlands.GaloisCohomology.PoitouTate.loc ι M 2))
  (exact_loc_locDual_two :
    Function.Exact ⇑(Langlands.GaloisCohomology.PoitouTate.loc ι M 2)
      ⇑(Langlands.GaloisCohomology.PoitouTate.locDual ι N M ⋯))
  (surjective_locDual_two : Function.Surjective ⇑(Langlands.GaloisCohomology.PoitouTate.locDual ι N M ⋯)) :
  Langlands.GaloisCohomology.PoitouTate.IsNineTermExact ι N M
Langlands.GaloisCohomology.PoitouTate.IsNineTermExact.rec.{u_1, u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  [Finite ↑S] {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} [Langlands.IsSmoothRep M]
  [Finite ↑M] {motive : Langlands.GaloisCohomology.PoitouTate.IsNineTermExact ι N M → Sort u_1}
  (mk :
    (injective_locHat : Function.Injective ⇑(Langlands.GaloisCohomology.PoitouTate.locHat ι M)) →
      (exact_locHat_locDualHat :
          Function.Exact ⇑(Langlands.GaloisCohomology.PoitouTate.locHat ι M)
            ⇑(Langlands.GaloisCohomology.PoitouTate.locDualHat ι N M)) →
        (exact_locDualHat_connecting :
            Function.Exact ⇑(Langlands.GaloisCohomology.PoitouTate.locDualHat ι N M)
              ⇑(Langlands.GaloisCohomology.PoitouTate.connecting ι N M ⋯)) →
          (exact_connecting_loc_one :
              Function.Exact ⇑(Langlands.GaloisCohomology.PoitouTate.connecting ι N M ⋯)
                ⇑(Langlands.GaloisCohomology.PoitouTate.loc ι M 1)) →
            (exact_loc_locDual_one :
                Function.Exact ⇑(Langlands.GaloisCohomology.PoitouTate.loc ι M 1)
                  ⇑(Langlands.GaloisCohomology.PoitouTate.locDual ι N M ⋯)) →
              (exact_locDual_connecting_one :
                  Function.Exact ⇑(Langlands.GaloisCohomology.PoitouTate.locDual ι N M ⋯)
                    ⇑(Langlands.GaloisCohomology.PoitouTate.connecting ι N M ⋯)) →
                (exact_connecting_loc_two :
                    Function.Exact ⇑(Langlands.GaloisCohomology.PoitouTate.connecting ι N M ⋯)
                      ⇑(Langlands.GaloisCohomology.PoitouTate.loc ι M 2)) →
                  (exact_loc_locDual_two :
                      Function.Exact ⇑(Langlands.GaloisCohomology.PoitouTate.loc ι M 2)
                        ⇑(Langlands.GaloisCohomology.PoitouTate.locDual ι N M ⋯)) →
                    (surjective_locDual_two :
                        Function.Surjective ⇑(Langlands.GaloisCohomology.PoitouTate.locDual ι N M ⋯)) →
                      motive ⋯)
  (t : Langlands.GaloisCohomology.PoitouTate.IsNineTermExact ι N M) : motive t
Langlands.GaloisCohomology.PoitouTate.IsNineTermExact.surjective_locDual_two.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} [Langlands.IsSmoothRep M]
  [Finite ↑M] (self : Langlands.GaloisCohomology.PoitouTate.IsNineTermExact ι N M) :
  Function.Surjective ⇑(Langlands.GaloisCohomology.PoitouTate.locDual ι N M ⋯)
Langlands.GaloisCohomology.PoitouTate.IsNineTermExact.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  [Finite ↑S] (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ) [NeZero N]
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] : Prop
Langlands.GaloisCohomology.PoitouTateNineTermStatement.{u} : Prop
```

## Outline of the proofs

Statement only.

## Declarations

`IsNineTermExact`, `PoitouTateNineTermStatement`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008, corrected printing 2013), chapter VIII, §6: Theorem (8.6.7) (Poitou–Tate duality), p. 485; Proposition (8.6.8) (the pairing through cup products), p. 487; (8.6.10) (the long exact sequence of Poitou–Tate, and the real places in degrees `≥ 3`), pp. 489–490.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter I, §4, Theorem 4.10, pp. 56–57; chapter II, §2, pp. 165–166 (cohomology with compact support).
