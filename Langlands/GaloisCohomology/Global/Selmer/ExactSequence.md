# The exact sequence of a Selmer group

`Langlands/GaloisCohomology/Global/Selmer/ExactSequence.lean`, namespace `Langlands.GaloisCohomology`.

Let `K` be a number field, `Ω` a separable closure, `S` a finite set of finite places containing the
places above `N ≥ 1`, `M` a finite smooth `G_S`-module killed by `N`, `M' = Hom(M, μ_N)`, `L` a family
of local conditions for `M` and `L^⊥ = L.dual N`. With `X^∨ = Hom(X, ℚ/ℤ)`, the maps

* `Sel_L(M) → H¹(G_S, M)`, the inclusion;
* `H¹(G_S, M) → P¹(M)/L` (`toLocalQuotient`);
* `P¹(M)/L → Sel_{L^⊥}(M')^∨` (`localQuotientToSelmerDual`), induced by `PoitouTate.locDual`, which
  vanishes on `L` against `Sel_{L^⊥}(M')` (`restrictDual_locDual_eq_zero`);
* `Sel_{L^⊥}(M')^∨ → H²(G_S, M)` (`selmerDualToCohomologyTwo`): extension of a character to
  `H¹(G_S, M')` (`surjective_restrictDual`) followed by the connecting map `PoitouTate.connecting`;
  the result does not depend on the extension (`selmerDualToCohomologyTwo_restrictDual`) since a
  character vanishing on `Ш¹_S(M')` is the sum of the local pairings with a family of local classes
  (`exists_locDual_eq`) and the connecting map kills those (`connecting_locDual_one` of `Langlands.GaloisCohomology.Global.PoitouTate.Corollaries`). Like
  `PoitouTate.connecting`, the definition takes no proof: it is `0` when the extension is not well
  defined, which does not happen under the hypotheses above;
* `H²(G_S, M) → P²(M) → H⁰(G_S, M')^∨`, the maps `PoitouTate.loc` and `PoitouTate.locDual`,

form the exact sequence

`0 → Sel_L(M) → H¹(G_S, M) → P¹(M)/L → Sel_{L^⊥}(M')^∨ → H²(G_S, M) → P²(M) → H⁰(G_S, M')^∨ → 0`

(`exact_subtype_toLocalQuotient`, `exact_toLocalQuotient_localQuotientToSelmerDual`,
`exact_localQuotientToSelmerDual_selmerDualToCohomologyTwo`, `exact_selmerDualToCohomologyTwo_loc`,
and the end of the nine-term sequence), and counting along it (`card_selmerGroup_mul_eq`)

`#Sel_L(M) · #P¹(M) · #H²(G_S, M) · #H⁰(G_S, M') = #H¹(G_S, M) · #Sel_{L^⊥}(M') · #P²(M) · #L`.

The image of the localization in degree one is the orthogonal of the image of the localization of
`M'` (`leftOrthogonal_range_loc` of `Langlands.GaloisCohomology.Global.PoitouTate.Corollaries`).

```lean
def toLocalQuotient : cohomology M 1 →+ LocalTerm ι M 1 ⧸ L.toLocalTerm
def restrictDual :
    (cohomology (PoitouTate.dual N M) 1 →+ QZ) →+ ((L.dual N).selmerGroup →+ QZ)
def localQuotientToSelmerDual :
    LocalTerm ι M 1 ⧸ L.toLocalTerm →+ ((L.dual N).selmerGroup →+ QZ)
def selmerDualToCohomologyTwo : ((L.dual N).selmerGroup →+ QZ) →+ cohomology M 2
theorem exact_subtype_toLocalQuotient :
    Function.Exact L.selmerGroup.subtype L.toLocalQuotient
theorem exact_toLocalQuotient_localQuotientToSelmerDual :
    Function.Exact L.toLocalQuotient (L.localQuotientToSelmerDual N)
theorem exact_localQuotientToSelmerDual_selmerDualToCohomologyTwo :
    Function.Exact (L.localQuotientToSelmerDual N) (L.selmerDualToCohomologyTwo N)
theorem exact_selmerDualToCohomologyTwo_loc :
    Function.Exact (L.selmerDualToCohomologyTwo N) (loc ι M 2)
theorem card_selmerGroup_mul_eq :
    Nat.card L.selmerGroup * Nat.card (LocalTerm ι M 1) * Nat.card (cohomology M 2) *
        Nat.card (cohomology (PoitouTate.dual N M) 0) =
      Nat.card (cohomology M 1) * Nat.card (L.dual N).selmerGroup * Nat.card (LocalTerm ι M 2) *
        Nat.card L.toLocalTerm
```

## Complete types

In the `#check` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.LocalConditions.toLocalQuotient : {K Ω : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [inst_4 : IsSepClosure K Ω] →
            {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} →
              {ι : Langlands.Galois.PlaceEmbeddings K Ω} →
                {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} →
                  [inst_5 : Langlands.IsSmoothRep M] →
                    (L : Langlands.GaloisCohomology.LocalConditions ι M) →
                      ↑(Langlands.ProfiniteCohomology.cohomology M 1) →+
                        Langlands.GaloisCohomology.PoitouTate.LocalTerm ι M 1 ⧸
                          Langlands.GaloisCohomology.LocalConditions.toLocalTerm L
@Langlands.GaloisCohomology.LocalConditions.toLocalQuotient_apply : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω}
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_5 : Langlands.IsSmoothRep M] (L : Langlands.GaloisCohomology.LocalConditions ι M)
  (x : ↑(Langlands.ProfiniteCohomology.cohomology M 1)),
  (Langlands.GaloisCohomology.LocalConditions.toLocalQuotient L) x =
    ↑((Langlands.GaloisCohomology.PoitouTate.loc ι M 1) x)
@Langlands.GaloisCohomology.LocalConditions.exact_subtype_toLocalQuotient : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω}
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_5 : Langlands.IsSmoothRep M] (L : Langlands.GaloisCohomology.LocalConditions ι M),
  Function.Exact ⇑(AddSubgroup.subtype (Langlands.GaloisCohomology.LocalConditions.selmerGroup L))
    ⇑(Langlands.GaloisCohomology.LocalConditions.toLocalQuotient L)
@Langlands.GaloisCohomology.LocalConditions.restrictDual : {K Ω : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [inst_4 : IsSepClosure K Ω] →
            {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} →
              {ι : Langlands.Galois.PlaceEmbeddings K Ω} →
                (N : ℕ) →
                  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} →
                    [inst_5 : Langlands.IsSmoothRep M] →
                      [inst_6 : Finite ↑M] →
                        (L : Langlands.GaloisCohomology.LocalConditions ι M) →
                          (↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dual N M)
                                  1) →+
                              Langlands.ProfiniteCohomology.QZ) →+
                            ↥(Langlands.GaloisCohomology.LocalConditions.selmerGroup
                                  (Langlands.GaloisCohomology.LocalConditions.dual N L)) →+
                              Langlands.ProfiniteCohomology.QZ
@Langlands.GaloisCohomology.LocalConditions.restrictDual_apply : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} (N : ℕ)
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_5 : Langlands.IsSmoothRep M] [inst_6 : Finite ↑M] (L : Langlands.GaloisCohomology.LocalConditions ι M)
  (χ :
    ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dual N M) 1) →+
      Langlands.ProfiniteCohomology.QZ)
  (y : ↥(Langlands.GaloisCohomology.LocalConditions.selmerGroup (Langlands.GaloisCohomology.LocalConditions.dual N L))),
  ((Langlands.GaloisCohomology.LocalConditions.restrictDual N L) χ) y = χ ↑y
@Langlands.GaloisCohomology.LocalConditions.surjective_restrictDual : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} (N : ℕ)
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_5 : Langlands.IsSmoothRep M] [inst_6 : Finite ↑M] (L : Langlands.GaloisCohomology.LocalConditions ι M),
  Function.Surjective ⇑(Langlands.GaloisCohomology.LocalConditions.restrictDual N L)
@Langlands.GaloisCohomology.LocalConditions.restrictDual_locDual_eq_zero : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [inst_5 : Finite ↑S]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} (N : ℕ)
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_6 : Langlands.IsSmoothRep M] [inst_7 : Finite ↑M] (L : Langlands.GaloisCohomology.LocalConditions ι M)
  {ξ : Langlands.GaloisCohomology.PoitouTate.LocalTerm ι M 1},
  ξ ∈ Langlands.GaloisCohomology.LocalConditions.toLocalTerm L →
    (Langlands.GaloisCohomology.LocalConditions.restrictDual N L)
        ((Langlands.GaloisCohomology.PoitouTate.locDual ι N M ⋯) ξ) =
      0
@Langlands.GaloisCohomology.LocalConditions.localQuotientToSelmerDual : {K Ω : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [inst_4 : IsSepClosure K Ω] →
            {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} →
              [Finite ↑S] →
                {ι : Langlands.Galois.PlaceEmbeddings K Ω} →
                  (N : ℕ) →
                    {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} →
                      [inst_6 : Langlands.IsSmoothRep M] →
                        [inst_7 : Finite ↑M] →
                          (L : Langlands.GaloisCohomology.LocalConditions ι M) →
                            Langlands.GaloisCohomology.PoitouTate.LocalTerm ι M 1 ⧸
                                Langlands.GaloisCohomology.LocalConditions.toLocalTerm L →+
                              ↥(Langlands.GaloisCohomology.LocalConditions.selmerGroup
                                    (Langlands.GaloisCohomology.LocalConditions.dual N L)) →+
                                Langlands.ProfiniteCohomology.QZ
@Langlands.GaloisCohomology.LocalConditions.localQuotientToSelmerDual_mk : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [inst_5 : Finite ↑S]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} (N : ℕ)
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_6 : Langlands.IsSmoothRep M] [inst_7 : Finite ↑M] (L : Langlands.GaloisCohomology.LocalConditions ι M)
  (ξ : Langlands.GaloisCohomology.PoitouTate.LocalTerm ι M 1),
  (Langlands.GaloisCohomology.LocalConditions.localQuotientToSelmerDual N L) ↑ξ =
    (Langlands.GaloisCohomology.LocalConditions.restrictDual N L)
      ((Langlands.GaloisCohomology.PoitouTate.locDual ι N M ⋯) ξ)
@Langlands.GaloisCohomology.LocalConditions.selmerDualToCohomologyTwo : {K Ω : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [inst_4 : IsSepClosure K Ω] →
            {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} →
              [Finite ↑S] →
                {ι : Langlands.Galois.PlaceEmbeddings K Ω} →
                  (N : ℕ) →
                    [NeZero N] →
                      {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} →
                        [inst_7 : Langlands.IsSmoothRep M] →
                          [inst_8 : Finite ↑M] →
                            (L : Langlands.GaloisCohomology.LocalConditions ι M) →
                              (↥(Langlands.GaloisCohomology.LocalConditions.selmerGroup
                                      (Langlands.GaloisCohomology.LocalConditions.dual N L)) →+
                                  Langlands.ProfiniteCohomology.QZ) →+
                                ↑(Langlands.ProfiniteCohomology.cohomology M 2)
@Langlands.GaloisCohomology.LocalConditions.exists_locDual_eq : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [inst_5 : Finite ↑S]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} (N : ℕ) [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_7 : Langlands.IsSmoothRep M] [inst_8 : Finite ↑M],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ↑N ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S) →
    (∀ (m : ↑M), N • m = 0) →
      ∀
        (χ :
          ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dual N M) 1) →+
            Langlands.ProfiniteCohomology.QZ),
        (∀ y ∈ Langlands.GaloisCohomology.sha ι (Langlands.GaloisCohomology.PoitouTate.dual N M) 1, χ y = 0) →
          ∃ ξ, (Langlands.GaloisCohomology.PoitouTate.locDual ι N M ⋯) ξ = χ
@Langlands.GaloisCohomology.LocalConditions.selmerDualToCohomologyTwo_restrictDual : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [inst_5 : Finite ↑S]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} (N : ℕ) [inst_6 : NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_7 : Langlands.IsSmoothRep M] [inst_8 : Finite ↑M] (L : Langlands.GaloisCohomology.LocalConditions ι M),
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ↑N ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S) →
    (∀ (m : ↑M), N • m = 0) →
      ∀
        (χ :
          ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dual N M) 1) →+
            Langlands.ProfiniteCohomology.QZ),
        (Langlands.GaloisCohomology.LocalConditions.selmerDualToCohomologyTwo N L)
            ((Langlands.GaloisCohomology.LocalConditions.restrictDual N L) χ) =
          (Langlands.GaloisCohomology.PoitouTate.connecting ι N M ⋯) χ
@Langlands.GaloisCohomology.LocalConditions.mem_range_loc_sup_of_locDual_eq_zero : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [inst_5 : Finite ↑S]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_7 : Langlands.IsSmoothRep M] [inst_8 : Finite ↑M] (L : Langlands.GaloisCohomology.LocalConditions ι M),
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ↑N ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S) →
    (∀ (m : ↑M), N • m = 0) →
      ∀ {ξ : Langlands.GaloisCohomology.PoitouTate.LocalTerm ι M 1},
        (∀
            y ∈
              Langlands.GaloisCohomology.LocalConditions.selmerGroup
                (Langlands.GaloisCohomology.LocalConditions.dual N L),
            ((Langlands.GaloisCohomology.PoitouTate.locDual ι N M ⋯) ξ) y = 0) →
          ξ ∈
            AddMonoidHom.range (Langlands.GaloisCohomology.PoitouTate.loc ι M 1) ⊔
              Langlands.GaloisCohomology.LocalConditions.toLocalTerm L
@Langlands.GaloisCohomology.LocalConditions.exists_toLocalQuotient_eq : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [inst_5 : Finite ↑S]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_7 : Langlands.IsSmoothRep M] [inst_8 : Finite ↑M] (L : Langlands.GaloisCohomology.LocalConditions ι M),
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ↑N ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S) →
    (∀ (m : ↑M), N • m = 0) →
      ∀ {ξ : Langlands.GaloisCohomology.PoitouTate.LocalTerm ι M 1},
        (Langlands.GaloisCohomology.LocalConditions.restrictDual N L)
              ((Langlands.GaloisCohomology.PoitouTate.locDual ι N M ⋯) ξ) =
            0 →
          ∃ x, (Langlands.GaloisCohomology.LocalConditions.toLocalQuotient L) x = ↑ξ
@Langlands.GaloisCohomology.LocalConditions.restrictDual_locDual_eq_zero_of_toLocalQuotient_eq : ∀ {K Ω : Type u}
  [inst : Field K] [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [inst_5 : Finite ↑S]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_7 : Langlands.IsSmoothRep M] [inst_8 : Finite ↑M] (L : Langlands.GaloisCohomology.LocalConditions ι M),
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ↑N ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S) →
    (∀ (m : ↑M), N • m = 0) →
      ∀ {ξ : Langlands.GaloisCohomology.PoitouTate.LocalTerm ι M 1}
        {x : ↑(Langlands.ProfiniteCohomology.cohomology M 1)},
        (Langlands.GaloisCohomology.LocalConditions.toLocalQuotient L) x = ↑ξ →
          (Langlands.GaloisCohomology.LocalConditions.restrictDual N L)
              ((Langlands.GaloisCohomology.PoitouTate.locDual ι N M ⋯) ξ) =
            0
@Langlands.GaloisCohomology.LocalConditions.exact_toLocalQuotient_localQuotientToSelmerDual : ∀ {K Ω : Type u}
  [inst : Field K] [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [inst_5 : Finite ↑S]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_7 : Langlands.IsSmoothRep M] [inst_8 : Finite ↑M] (L : Langlands.GaloisCohomology.LocalConditions ι M),
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ↑N ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S) →
    (∀ (m : ↑M), N • m = 0) →
      Function.Exact ⇑(Langlands.GaloisCohomology.LocalConditions.toLocalQuotient L)
        ⇑(Langlands.GaloisCohomology.LocalConditions.localQuotientToSelmerDual N L)
@Langlands.GaloisCohomology.LocalConditions.exists_localQuotientToSelmerDual_eq : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [inst_5 : Finite ↑S]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [inst_6 : NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_7 : Langlands.IsSmoothRep M] [inst_8 : Finite ↑M] (L : Langlands.GaloisCohomology.LocalConditions ι M),
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ↑N ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S) →
    (∀ (m : ↑M), N • m = 0) →
      ∀
        {χ :
          ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dual N M) 1) →+
            Langlands.ProfiniteCohomology.QZ},
        (Langlands.GaloisCohomology.PoitouTate.connecting ι N M ⋯) χ = 0 →
          ∃ q,
            (Langlands.GaloisCohomology.LocalConditions.localQuotientToSelmerDual N L) q =
              (Langlands.GaloisCohomology.LocalConditions.restrictDual N L) χ
@Langlands.GaloisCohomology.LocalConditions.selmerDualToCohomologyTwo_localQuotientToSelmerDual : ∀ {K Ω : Type u}
  [inst : Field K] [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [inst_5 : Finite ↑S]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [inst_6 : NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_7 : Langlands.IsSmoothRep M] [inst_8 : Finite ↑M] (L : Langlands.GaloisCohomology.LocalConditions ι M),
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ↑N ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S) →
    (∀ (m : ↑M), N • m = 0) →
      ∀
        (q :
          Langlands.GaloisCohomology.PoitouTate.LocalTerm ι M 1 ⧸
            Langlands.GaloisCohomology.LocalConditions.toLocalTerm L),
        (Langlands.GaloisCohomology.LocalConditions.selmerDualToCohomologyTwo N L)
            ((Langlands.GaloisCohomology.LocalConditions.localQuotientToSelmerDual N L) q) =
          0
@Langlands.GaloisCohomology.LocalConditions.exact_localQuotientToSelmerDual_selmerDualToCohomologyTwo : ∀ {K Ω : Type u}
  [inst : Field K] [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [inst_5 : Finite ↑S]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [inst_6 : NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_7 : Langlands.IsSmoothRep M] [inst_8 : Finite ↑M] (L : Langlands.GaloisCohomology.LocalConditions ι M),
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ↑N ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S) →
    (∀ (m : ↑M), N • m = 0) →
      Function.Exact ⇑(Langlands.GaloisCohomology.LocalConditions.localQuotientToSelmerDual N L)
        ⇑(Langlands.GaloisCohomology.LocalConditions.selmerDualToCohomologyTwo N L)
@Langlands.GaloisCohomology.LocalConditions.exact_selmerDualToCohomologyTwo_loc : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [inst_5 : Finite ↑S]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [inst_6 : NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_7 : Langlands.IsSmoothRep M] [inst_8 : Finite ↑M] (L : Langlands.GaloisCohomology.LocalConditions ι M),
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ↑N ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S) →
    (∀ (m : ↑M), N • m = 0) →
      Function.Exact ⇑(Langlands.GaloisCohomology.LocalConditions.selmerDualToCohomologyTwo N L)
        ⇑(Langlands.GaloisCohomology.PoitouTate.loc ι M 2)
@Langlands.GaloisCohomology.LocalConditions.card_selmerGroup_mul_eq : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_7 : Langlands.IsSmoothRep M] [inst_8 : Finite ↑M] (L : Langlands.GaloisCohomology.LocalConditions ι M),
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ↑N ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S) →
    (∀ (m : ↑M), N • m = 0) →
      Nat.card ↥(Langlands.GaloisCohomology.LocalConditions.selmerGroup L) *
              Nat.card (Langlands.GaloisCohomology.PoitouTate.LocalTerm ι M 1) *
            Nat.card ↑(Langlands.ProfiniteCohomology.cohomology M 2) *
          Nat.card ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dual N M) 0) =
        Nat.card ↑(Langlands.ProfiniteCohomology.cohomology M 1) *
              Nat.card
                ↥(Langlands.GaloisCohomology.LocalConditions.selmerGroup
                    (Langlands.GaloisCohomology.LocalConditions.dual N L)) *
            Nat.card (Langlands.GaloisCohomology.PoitouTate.LocalTerm ι M 2) *
          Nat.card ↥(Langlands.GaloisCohomology.LocalConditions.toLocalTerm L)
```

## Outline of the proofs

The nine-term exact sequence of Poitou–Tate is `poitouTateNineTermStatement` of
`Langlands.GaloisCohomology.Global.PoitouTate.NineTermProof`.

- `connecting_locDual_one` holds without hypothesis: if the duality map `Ĥ_c² → H¹(M')^∨` is
  bijective, on the image of `P¹(M)` it is `locDual` (`compactDualityMap_localToCompact`) and
  `P¹(M) → Ĥ_c²(G_S, M) → H²(G_S, M)` vanishes; otherwise the connecting map is `0`.
- Exactness at `P¹(M)/L`: if `locDual ξ` vanishes on `Sel_{L^⊥}(M')`, then `ξ` is orthogonal to
  `loc(H¹(G_S, M')) ∩ L^⊥` for the sum of the local pairings, which is perfect
  (`bijective_localTermPairing`); the orthogonal of the intersection is
  `⊥loc(H¹(G_S, M')) + ⊥L^⊥ = loc(H¹(G_S, M)) + L` by `leftOrthogonal_inf`, the exactness of the
  nine-term sequence at `P¹(M)` (`leftOrthogonal_range_loc`) and `leftOrthogonal_rightOrthogonal`.
- Exactness at `Sel_{L^⊥}(M')^∨` and at `H²(G_S, M)`: the exactness of the nine-term sequence at
  `H¹(G_S, M')^∨` and at `H²(G_S, M)`, through the surjective restriction `H¹(G_S, M')^∨ → Sel^∨`.
- The count: `card_mul_card_eq_of_exact_seven`, `#X^∨ = #X` and `#(P¹/L) · #L = #P¹`.

## Declarations

`LocalConditions.toLocalQuotient`, `LocalConditions.toLocalQuotient_apply`, `LocalConditions.exact_subtype_toLocalQuotient`, `LocalConditions.restrictDual`, `LocalConditions.restrictDual_apply`, `LocalConditions.surjective_restrictDual`, `LocalConditions.restrictDual_locDual_eq_zero`, `LocalConditions.localQuotientToSelmerDual`, `LocalConditions.localQuotientToSelmerDual_mk`, `LocalConditions.selmerDualToCohomologyTwo`, `LocalConditions.exists_locDual_eq`, `LocalConditions.selmerDualToCohomologyTwo_restrictDual`, `LocalConditions.mem_range_loc_sup_of_locDual_eq_zero`, `LocalConditions.exists_toLocalQuotient_eq`, `LocalConditions.restrictDual_locDual_eq_zero_of_toLocalQuotient_eq`, `LocalConditions.exact_toLocalQuotient_localQuotientToSelmerDual`, `LocalConditions.exists_localQuotientToSelmerDual_eq`, `LocalConditions.selmerDualToCohomologyTwo_localQuotientToSelmerDual`, `LocalConditions.exact_localQuotientToSelmerDual_selmerDualToCohomologyTwo`, `LocalConditions.exact_selmerDualToCohomologyTwo_loc`, `LocalConditions.card_selmerGroup_mul_eq`.

## References

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed. (Springer 2008, corrected printing 2013), (8.7.9) and its proof, pp. 512–513 (an exact sequence of the same kind, built there on the
  beginning of the nine-term sequence).
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed. (BookSurge 2006), I §4, Theorem 4.10, p. 56 (the nine-term sequence).
