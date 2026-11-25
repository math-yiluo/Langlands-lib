# The formula of Greenberg and Wiles: proof

`Langlands/GaloisCohomology/Global/Selmer/GreenbergWilesProof.lean`, namespace `Langlands.GaloisCohomology`.

`greenbergWilesStatement : GreenbergWilesStatement`: the formula of Greenberg and Wiles for every
number field, every finite set `S` of finite places containing the places above `N`, every finite
smooth `G_S`-module killed by `N` and every family of local conditions. Multiplied out
(`LocalConditions.card_selmerGroup_mul_eq_card_selmerGroup_dual_mul`):

`#Sel_L(M) · #H⁰(G_S, M') · ∏_{v ∈ S} #H⁰(K_v, M) · ∏_{w real} #H⁰(K_w, M) · (#M)^{r₂} =
 #Sel_{L^⊥}(M') · #H⁰(G_S, M) · ∏_{v ∈ S} #L_v · ∏_{w real} #L_w`,

and as a quotient (`LocalConditions.card_selmerGroup_div_card_selmerGroup_dual`). On the way:
`#Pⁿ(M) = ∏_{v ∈ S} #Hⁿ(K_v, M) · ∏_{w real} #Hⁿ(K_w, M)` (`card_localTerm`), the local Euler
characteristic over `S` with the product formula (`prod_card_cohomology_one_localModule`) and the
Herbrand quotient at the real places (`prod_card_cohomology_one_realLocalModule`).

```lean
theorem card_localTerm (n : ℕ) :
    Nat.card (LocalTerm ι M n) = letI : Fintype S
theorem prod_card_cohomology_one_localModule
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card M : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    letI : Fintype S
theorem prod_card_cohomology_one_realLocalModule :
    ∏ w : {w : InfinitePlace K // w.IsReal}, Nat.card (cohomology (realLocalModule ι M w.1) 1) =
      ∏ w : {w : InfinitePlace K // w.IsReal}, Nat.card (cohomology (realLocalModule ι M w.1) 2)
theorem card_selmerGroup_mul_eq_card_selmerGroup_dual_mul
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hM : ∀ m : M, N • m = 0) (L : LocalConditions ι M) :
    letI : Fintype S
theorem card_selmerGroup_div_card_selmerGroup_dual
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hM : ∀ m : M, N • m = 0) (L : LocalConditions ι M) :
    letI : Fintype S
theorem greenbergWilesStatement : GreenbergWilesStatement.{u}
```

## Complete types

In the `#check` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.card_localTerm : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [inst_5 : Finite ↑S]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
  [inst_6 : Langlands.IsSmoothRep M] (n : ℕ),
  Nat.card (Langlands.GaloisCohomology.PoitouTate.LocalTerm ι M n) =
    (∏ v, Nat.card ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.localModule ι M ↑v) n)) *
      ∏ w, Nat.card ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.realLocalModule ι M ↑w) n)
@Langlands.GaloisCohomology.prod_card_cohomology_one_localModule : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [inst_5 : Finite ↑S]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
  [inst_6 : Langlands.IsSmoothRep M] [Finite ↑M],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ↑(Nat.card ↑M) ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S) →
    ∏ v, Nat.card ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.localModule ι M ↑v) 1) =
      ((∏ v, Nat.card ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.localModule ι M ↑v) 0)) *
          ∏ v, Nat.card ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.localModule ι M ↑v) 2)) *
        Nat.card ↑M ^ Module.finrank ℚ K
@Langlands.GaloisCohomology.prod_card_cohomology_one_realLocalModule : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
  [inst_5 : Langlands.IsSmoothRep M] [Finite ↑M],
  ∏ w, Nat.card ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.realLocalModule ι M ↑w) 1) =
    ∏ w, Nat.card ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.realLocalModule ι M ↑w) 2)
@Langlands.GaloisCohomology.LocalConditions.card_selmerGroup_mul_eq_card_selmerGroup_dual_mul : ∀ {K Ω : Type u}
  [inst : Field K] [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [inst_5 : Finite ↑S]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_7 : Langlands.IsSmoothRep M] [inst_8 : Finite ↑M],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ↑N ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S) →
    (∀ (m : ↑M), N • m = 0) →
      ∀ (L : Langlands.GaloisCohomology.LocalConditions ι M),
        ((Nat.card ↥(Langlands.GaloisCohomology.LocalConditions.selmerGroup L) *
                  Nat.card
                    ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dual N M) 0) *
                ∏ v,
                  Nat.card
                    ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.localModule ι M ↑v) 0)) *
              ∏ w,
                Nat.card
                  ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.realLocalModule ι M ↑w) 0)) *
            Nat.card ↑M ^ NumberField.InfinitePlace.nrComplexPlaces K =
          (Nat.card
                  ↥(Langlands.GaloisCohomology.LocalConditions.selmerGroup
                      (Langlands.GaloisCohomology.LocalConditions.dual N L)) *
                Nat.card ↑(Langlands.ProfiniteCohomology.cohomology M 0) *
              ∏ v, Nat.card ↥(Langlands.GaloisCohomology.LocalConditions.finite L v)) *
            ∏ w, Nat.card ↥(Langlands.GaloisCohomology.LocalConditions.real L w)
@Langlands.GaloisCohomology.LocalConditions.card_selmerGroup_div_card_selmerGroup_dual : ∀ {K Ω : Type u}
  [inst : Field K] [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [inst_5 : Finite ↑S]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_7 : Langlands.IsSmoothRep M] [inst_8 : Finite ↑M],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ↑N ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S) →
    (∀ (m : ↑M), N • m = 0) →
      ∀ (L : Langlands.GaloisCohomology.LocalConditions ι M),
        ↑(Nat.card ↥(Langlands.GaloisCohomology.LocalConditions.selmerGroup L)) /
            ↑(Nat.card
                ↥(Langlands.GaloisCohomology.LocalConditions.selmerGroup
                    (Langlands.GaloisCohomology.LocalConditions.dual N L))) =
          ((↑(Nat.card ↑(Langlands.ProfiniteCohomology.cohomology M 0)) /
                  ↑(Nat.card
                      ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dual N M) 0)) *
                ∏ v,
                  ↑(Nat.card ↥(Langlands.GaloisCohomology.LocalConditions.finite L v)) /
                    ↑(Nat.card
                        ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.localModule ι M ↑v)
                            0))) *
              ∏ w,
                ↑(Nat.card ↥(Langlands.GaloisCohomology.LocalConditions.real L w)) /
                  ↑(Nat.card
                      ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.realLocalModule ι M ↑w)
                          0))) /
            ↑(Nat.card ↑M) ^ NumberField.InfinitePlace.nrComplexPlaces K
@Langlands.GaloisCohomology.greenbergWilesStatement : Langlands.GaloisCohomology.GreenbergWilesStatement
```

## Outline of the proofs

The way of Neukirch–Schmidt–Wingberg (8.7.9), with the end of the nine-term sequence of Poitou–Tate in
place of its beginning:

- the exact sequence of `Langlands.GaloisCohomology.Global.Selmer.ExactSequence` gives
  `#Sel_L(M) · #P¹(M) · #H²(G_S, M) · #H⁰(G_S, M') = #H¹(G_S, M) · #Sel_{L^⊥}(M') · #P²(M) · #L`;
- the global Euler characteristic formula (`card_cohomology_one_mul_prod`) gives
  `#H¹(G_S, M) · ∏_{w real} #H⁰(K_w, M) = #H⁰(G_S, M) · #H²(G_S, M) · (#M)^{r₁ + r₂}`;
- `#P¹(M) = ∏_v #H⁰(K_v, M) · ∏_v #H²(K_v, M) · (#M)^{r₁ + 2r₂} · ∏_w #H²(K_w, M)` and
  `#P²(M) = ∏_v #H²(K_v, M) · ∏_w #H²(K_w, M)`.

Multiplying the first identity by `∏_w #H⁰(K_w, M)` and substituting the second, the factor
`∏_v #H²(K_v, M) · ∏_w #H²(K_w, M) · #H²(G_S, M) · (#M)^{r₁ + r₂}` (positive) cancels: a
`linear_combination` over `ℤ` after `Nat.eq_of_mul_eq_mul_right`. The quotient form follows by
`field_simp`, all orders being positive.

## Declarations

`card_localTerm`, `prod_card_cohomology_one_localModule`, `prod_card_cohomology_one_realLocalModule`, `LocalConditions.card_selmerGroup_mul_eq_card_selmerGroup_dual_mul`, `LocalConditions.card_selmerGroup_div_card_selmerGroup_dual`, `greenbergWilesStatement`.

## References

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed. (Springer 2008, corrected printing 2013), (8.7.9) and its proof, pp. 512–513; (8.7.4) (the global Euler characteristic), p. 505.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed. (BookSurge 2006), I §5, Theorem 5.1, p. 67 (the global Euler characteristic).
