# The formula of Greenberg and Wiles: statement

`Langlands/GaloisCohomology/Global/Selmer/GreenbergWilesStatement.lean`, namespace `Langlands.GaloisCohomology`.

Let `K` be a number field, `Ω` a separable closure, `S` a finite set of finite places of `K`
containing the places above `N ≥ 1`, `G_S = Gal(K_S/K)`, `M` a finite smooth `G_S`-module killed by
`N` with dual `M' = Hom(M, μ_N)`, and `L` a family of local conditions for `M` (subgroups
`L_v ⊆ H¹(K_v, M)` for `v ∈ S` and `L_w ⊆ H¹(K_w, M)` for the real places `w`) with dual family
`L^⊥` (the orthogonal complements under the local pairings of the Poitou–Tate sequence). The formula
of Greenberg and Wiles is

`#Sel_L(M) / #Sel_{L^⊥}(M') = #H⁰(G_S, M) / #H⁰(G_S, M') · ∏_{v ∈ S} #L_v / #H⁰(K_v, M)
  · ∏_{w real} #L_w / #H⁰(K_w, M) / (#M)^{r₂}`,

`r₂` the number of complex places of `K` (`InfinitePlace.nrComplexPlaces`). `GreenbergWilesStatement`
asserts it for all `K`, `Ω`, `S`, `ι`, `N`, `M` and every family of local conditions. It is proved in
`Langlands.GaloisCohomology.Global.Selmer.GreenbergWilesProof` (`greenbergWilesStatement`).

The formula is that of Neukirch–Schmidt–Wingberg (8.7.9), whose product runs over all places,
archimedean ones included, with `H⁰` (not `Ĥ⁰`) at the real places: the places outside `S` contribute
`1`, and a complex place contributes `1/#M`, since there `H⁰(K_w, M) = M` and `H¹(K_w, M) = 0`. For
`K = ℚ` there is no complex place.

```lean
def GreenbergWilesStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] (ι : PlaceEmbeddings K Ω) (N : ℕ) [NeZero N],
    (∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) →
    ∀ (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M],
      (∀ m : M, N • m = 0) → ∀ L : LocalConditions ι M,
        haveI : Fintype S := Fintype.ofFinite S
        (Nat.card L.selmerGroup : ℚ) / Nat.card (L.dual N).selmerGroup =
          (Nat.card (cohomology M 0) : ℚ) / Nat.card (cohomology (PoitouTate.dual N M) 0) *
            (∏ v : S, (Nat.card (L.finite v) : ℚ) / Nat.card (cohomology (localModule ι M v) 0)) *
            (∏ w : {w : InfinitePlace K // w.IsReal},
              (Nat.card (L.real w) : ℚ) / Nat.card (cohomology (realLocalModule ι M w.1) 0)) /
            (Nat.card M : ℚ) ^ InfinitePlace.nrComplexPlaces K
```

## Complete types

In the `#check` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.GreenbergWilesStatement : Prop
```

## Outline of the proofs

This file is a statement only.

## Declarations

`GreenbergWilesStatement`.

## References

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed. (Springer 2008, corrected printing 2013), (8.7.8), p. 511, and (8.7.9), p. 512.
