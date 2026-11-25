# Selmer groups

`Langlands/GaloisCohomology/Global/Selmer/SelmerGroup.lean`, namespace `Langlands.GaloisCohomology`.

Let `K` be a number field, `Ω` a separable closure, `S` a finite set of finite places of `K`,
`G_S = Gal(K_S/K)`, `M` a smooth `G_S`-module and `L` a family of local conditions for `M`
(`LocalConditions`). The Selmer group of `L` is

`Sel_L(M) = {x ∈ H¹(G_S, M) | loc_v(x) ∈ L_v for v ∈ S and loc_w(x) ∈ L_w for w real}`,

the preimage of `L.toLocalTerm ⊆ P¹(M)` under the localization `PoitouTate.loc ι M 1` of the
Poitou–Tate sequence (`LocalConditions.selmerGroup`, `LocalConditions.mem_selmerGroup`). It grows with
`L` (`selmerGroup_mono`) and contains `Ш¹_S(M)` (`sha_le_selmerGroup`); for the zero family it is
`Ш¹_S(M) = sha ι M 1` of `Langlands.GaloisCohomology.Global.Localization`
(`LocalConditions.selmerGroup_bot`) and for the full family it is `H¹(G_S, M)`
(`LocalConditions.selmerGroup_top`). It is finite when `M` is finite and `S` contains the places
above `#M` (`finite_selmerGroup`).

```lean
def selmerGroup (L : LocalConditions ι M) : AddSubgroup (cohomology M 1)
theorem mem_selmerGroup {L : LocalConditions ι M} {x : cohomology M 1} :
    x ∈ L.selmerGroup ↔ (∀ v : S, localization ι M v 1 x ∈ L.finite v) ∧
      ∀ w : {w : InfinitePlace K // w.IsReal}, realLocalization ι M w.1 1 x ∈ L.real w
theorem selmerGroup_bot : (⊥ : LocalConditions ι M).selmerGroup = sha ι M 1
theorem selmerGroup_top : (⊤ : LocalConditions ι M).selmerGroup = ⊤
theorem sha_le_selmerGroup (L : LocalConditions ι M) : sha ι M 1 ≤ L.selmerGroup
theorem finite_selmerGroup [Finite S] [Finite M]
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card M : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (L : LocalConditions ι M) : Finite L.selmerGroup
```

## Complete types

In the `#check` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.LocalConditions.selmerGroup : {K Ω : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [inst_4 : IsSepClosure K Ω] →
            {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} →
              {ι : Langlands.Galois.PlaceEmbeddings K Ω} →
                {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} →
                  [inst_5 : Langlands.IsSmoothRep M] →
                    Langlands.GaloisCohomology.LocalConditions ι M →
                      AddSubgroup ↑(Langlands.ProfiniteCohomology.cohomology M 1)
@Langlands.GaloisCohomology.LocalConditions.mem_selmerGroup_iff_loc_mem : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω}
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_5 : Langlands.IsSmoothRep M] {L : Langlands.GaloisCohomology.LocalConditions ι M}
  {x : ↑(Langlands.ProfiniteCohomology.cohomology M 1)},
  x ∈ Langlands.GaloisCohomology.LocalConditions.selmerGroup L ↔
    (Langlands.GaloisCohomology.PoitouTate.loc ι M 1) x ∈ Langlands.GaloisCohomology.LocalConditions.toLocalTerm L
@Langlands.GaloisCohomology.LocalConditions.mem_selmerGroup : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω}
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_5 : Langlands.IsSmoothRep M] {L : Langlands.GaloisCohomology.LocalConditions ι M}
  {x : ↑(Langlands.ProfiniteCohomology.cohomology M 1)},
  x ∈ Langlands.GaloisCohomology.LocalConditions.selmerGroup L ↔
    (∀ (v : ↑S),
        (Langlands.GaloisCohomology.localization ι M (↑v) 1) x ∈
          Langlands.GaloisCohomology.LocalConditions.finite L v) ∧
      ∀ (w : { w // NumberField.InfinitePlace.IsReal w }),
        (Langlands.GaloisCohomology.realLocalization ι M (↑w) 1) x ∈ Langlands.GaloisCohomology.LocalConditions.real L w
@Langlands.GaloisCohomology.LocalConditions.selmerGroup_mono : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω}
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_5 : Langlands.IsSmoothRep M] {L L' : Langlands.GaloisCohomology.LocalConditions ι M},
  L ≤ L' →
    Langlands.GaloisCohomology.LocalConditions.selmerGroup L ≤ Langlands.GaloisCohomology.LocalConditions.selmerGroup L'
@Langlands.GaloisCohomology.LocalConditions.selmerGroup_bot : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω}
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_5 : Langlands.IsSmoothRep M],
  Langlands.GaloisCohomology.LocalConditions.selmerGroup ⊥ = Langlands.GaloisCohomology.sha ι M 1
@Langlands.GaloisCohomology.LocalConditions.selmerGroup_top : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω}
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_5 : Langlands.IsSmoothRep M], Langlands.GaloisCohomology.LocalConditions.selmerGroup ⊤ = ⊤
@Langlands.GaloisCohomology.LocalConditions.sha_le_selmerGroup : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω}
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_5 : Langlands.IsSmoothRep M] (L : Langlands.GaloisCohomology.LocalConditions ι M),
  Langlands.GaloisCohomology.sha ι M 1 ≤ Langlands.GaloisCohomology.LocalConditions.selmerGroup L
@Langlands.GaloisCohomology.LocalConditions.finite_selmerGroup : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω}
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_5 : Langlands.IsSmoothRep M] [Finite ↑S] [Finite ↑M],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ↑(Nat.card ↑M) ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S) →
    ∀ (L : Langlands.GaloisCohomology.LocalConditions ι M),
      Finite ↥(Langlands.GaloisCohomology.LocalConditions.selmerGroup L)
```

## Outline of the proofs

`mem_selmerGroup` is `PoitouTate.loc_apply`; `selmerGroup_bot` is `PoitouTate.mem_sha_iff_loc_eq_zero`
(`Ш¹_S(M)` is the kernel of `loc`); finiteness is `finite_cohomology_of_le_two`.

## Declarations

`LocalConditions.selmerGroup`, `LocalConditions.mem_selmerGroup_iff_loc_mem`, `LocalConditions.mem_selmerGroup`, `LocalConditions.selmerGroup_mono`, `LocalConditions.selmerGroup_bot`, `LocalConditions.selmerGroup_top`, `LocalConditions.sha_le_selmerGroup`, `LocalConditions.finite_selmerGroup`.

## References

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed. (Springer 2008, corrected printing 2013), (8.7.8) (the groups `H¹_L(k, A)`), p. 511, and the description over `G_S`, p. 512.
