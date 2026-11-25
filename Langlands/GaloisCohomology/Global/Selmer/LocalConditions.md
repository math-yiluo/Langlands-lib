# Local conditions and their orthogonal complements

`Langlands/GaloisCohomology/Global/Selmer/LocalConditions.lean`, namespace `Langlands.GaloisCohomology`.

Let `K` be a number field, `Ω` a separable closure, `S` a finite set of finite places of `K`,
`G_S = Gal(K_S/K)` and `M` a smooth `G_S`-module. A family of local conditions for `M`
(`LocalConditions ι M`) is a subgroup `L_v ⊆ H¹(K_v, M)` for every `v ∈ S` (`finite`) and a subgroup
`L_w ⊆ H¹(K_w, M)` for every real place `w` (`real`). The families are ordered place by place
(a `PartialOrder`), with the zero family `⊥` and the full family `⊤`. Their product
`L.toLocalTerm` is a subgroup of `P¹(M) = ∏_{v ∈ S} H¹(K_v, M) × ∏_{w real} H¹(K_w, M)`
(`PoitouTate.LocalTerm`), of order `∏ #L_v · ∏ #L_w` (`card_toLocalTerm`).

For `N ≥ 1`, `M` finite and `M' = Hom(M, μ_N)`, the dual family `L.dual N` of conditions for `M'` is
the family of orthogonal complements `L_v^⊥`, `L_w^⊥` under the local pairings `localPairing`,
`realLocalPairing` of `PoitouTate.locDual` in degrees `1 + 1`; its product is the orthogonal of
`L.toLocalTerm` under the sum of the local pairings (`toLocalTerm_dual`). In the other direction
`L'.predual N` is the family of left orthogonal complements of a family `L'` for `M'`
(`toLocalTerm_predual`). When `S` contains the places above `N` and `N` kills `M`:

* `(L^⊥)^⊥ = L`: `(L.dual N).predual N = L` and `(L'.predual N).dual N = L'` (`predual_dual`,
  `dual_predual`); the form with `M'' = Hom(M', μ_N)` identified with `M` is `dual_dual` of
  `Langlands.GaloisCohomology.Global.Selmer.Bidual`;
* `#L_v · #L_v^⊥ = #H¹(K_v, M)` and `#L_w · #L_w^⊥ = #H¹(K_w, M)`
  (`card_finite_mul_card_dual_finite`, `card_real_mul_card_dual_real`);
* the zero family and the full family are dual to each other (`dual_bot`, which holds in general,
  and `dual_top`).

```lean
structure LocalConditions (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S))
    [IsSmoothRep M]
def toLocalTerm (L : LocalConditions ι M) : AddSubgroup (LocalTerm ι M 1)
theorem card_toLocalTerm [Finite S] (L : LocalConditions ι M) :
    Nat.card L.toLocalTerm = letI : Fintype S
def dual (L : LocalConditions ι M) : LocalConditions ι (PoitouTate.dual N M)
def predual (L' : LocalConditions ι (PoitouTate.dual N M)) : LocalConditions ι M
theorem toLocalTerm_dual (L : LocalConditions ι M) :
    (L.dual N).toLocalTerm = rightOrthogonal (localTermPairing ι N M) L.toLocalTerm
theorem predual_dual (L : LocalConditions ι M) : (L.dual N).predual N = L
theorem dual_predual (L' : LocalConditions ι (PoitouTate.dual N M)) : (L'.predual N).dual N = L'
theorem card_finite_mul_card_dual_finite (L : LocalConditions ι M) (v : S) :
    Nat.card (L.finite v) * Nat.card ((L.dual N).finite v) =
      Nat.card (cohomology (localModule ι M v) 1)
theorem card_real_mul_card_dual_real (L : LocalConditions ι M)
    (w : {w : InfinitePlace K // w.IsReal}) :
    Nat.card (L.real w) * Nat.card ((L.dual N).real w) =
      Nat.card (cohomology (realLocalModule ι M w.1) 1)
theorem dual_bot : (⊥ : LocalConditions ι M).dual N = ⊤
theorem dual_top : (⊤ : LocalConditions ι M).dual N = ⊥
```

## Complete types

In the `#check` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.LocalConditions : {K Ω : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [IsSepClosure K Ω] →
            {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} →
              Langlands.Galois.PlaceEmbeddings K Ω →
                (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) →
                  [Langlands.IsSmoothRep M] → Type u
@Langlands.GaloisCohomology.LocalConditions.casesOn : {K Ω : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [inst_4 : IsSepClosure K Ω] →
            {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} →
              {ι : Langlands.Galois.PlaceEmbeddings K Ω} →
                {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} →
                  [inst_5 : Langlands.IsSmoothRep M] →
                    {motive : Langlands.GaloisCohomology.LocalConditions ι M → Sort u_1} →
                      (t : Langlands.GaloisCohomology.LocalConditions ι M) →
                        ((finite :
                              (v : ↑S) →
                                AddSubgroup
                                  ↑(Langlands.ProfiniteCohomology.cohomology
                                      (Langlands.GaloisCohomology.localModule ι M ↑v) 1)) →
                            (real :
                                (w : { w // NumberField.InfinitePlace.IsReal w }) →
                                  AddSubgroup
                                    ↑(Langlands.ProfiniteCohomology.cohomology
                                        (Langlands.GaloisCohomology.realLocalModule ι M ↑w) 1)) →
                              motive { finite := finite, real := real }) →
                          motive t
@Langlands.GaloisCohomology.LocalConditions.noConfusion : {P : Sort u_1} →
  {K Ω : Type u} →
    {inst : Field K} →
      {inst_1 : NumberField K} →
        {inst_2 : Field Ω} →
          {inst_3 : Algebra K Ω} →
            {inst_4 : IsSepClosure K Ω} →
              {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} →
                {ι : Langlands.Galois.PlaceEmbeddings K Ω} →
                  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} →
                    {inst_5 : Langlands.IsSmoothRep M} →
                      {t : Langlands.GaloisCohomology.LocalConditions ι M} →
                        {K' Ω' : Type u} →
                          {inst' : Field K'} →
                            {inst'_1 : NumberField K'} →
                              {inst'_2 : Field Ω'} →
                                {inst'_3 : Algebra K' Ω'} →
                                  {inst'_4 : IsSepClosure K' Ω'} →
                                    {S' : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K'))} →
                                      {ι' : Langlands.Galois.PlaceEmbeddings K' Ω'} →
                                        {M' :
                                            Rep.{u, u, u} (ULift.{u, 0} ℤ)
                                              (Langlands.Galois.GaloisGroupUnramifiedOutside K' Ω' S')} →
                                          {inst'_5 : Langlands.IsSmoothRep M'} →
                                            {t' : Langlands.GaloisCohomology.LocalConditions ι' M'} →
                                              K = K' →
                                                Ω = Ω' →
                                                  inst ≍ inst' →
                                                    inst_1 ≍ inst'_1 →
                                                      inst_2 ≍ inst'_2 →
                                                        inst_3 ≍ inst'_3 →
                                                          inst_4 ≍ inst'_4 →
                                                            S ≍ S' →
                                                              ι ≍ ι' →
                                                                M ≍ M' →
                                                                  inst_5 ≍ inst'_5 →
                                                                    t ≍ t' →
                                                                      Langlands.GaloisCohomology.LocalConditions.noConfusionType
                                                                        P t t'
@Langlands.GaloisCohomology.LocalConditions.rec : {K Ω : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [inst_4 : IsSepClosure K Ω] →
            {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} →
              {ι : Langlands.Galois.PlaceEmbeddings K Ω} →
                {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} →
                  [inst_5 : Langlands.IsSmoothRep M] →
                    {motive : Langlands.GaloisCohomology.LocalConditions ι M → Sort u_1} →
                      ((finite :
                            (v : ↑S) →
                              AddSubgroup
                                ↑(Langlands.ProfiniteCohomology.cohomology
                                    (Langlands.GaloisCohomology.localModule ι M ↑v) 1)) →
                          (real :
                              (w : { w // NumberField.InfinitePlace.IsReal w }) →
                                AddSubgroup
                                  ↑(Langlands.ProfiniteCohomology.cohomology
                                      (Langlands.GaloisCohomology.realLocalModule ι M ↑w) 1)) →
                            motive { finite := finite, real := real }) →
                        (t : Langlands.GaloisCohomology.LocalConditions ι M) → motive t
@Langlands.GaloisCohomology.LocalConditions.recOn : {K Ω : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [inst_4 : IsSepClosure K Ω] →
            {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} →
              {ι : Langlands.Galois.PlaceEmbeddings K Ω} →
                {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} →
                  [inst_5 : Langlands.IsSmoothRep M] →
                    {motive : Langlands.GaloisCohomology.LocalConditions ι M → Sort u_1} →
                      (t : Langlands.GaloisCohomology.LocalConditions ι M) →
                        ((finite :
                              (v : ↑S) →
                                AddSubgroup
                                  ↑(Langlands.ProfiniteCohomology.cohomology
                                      (Langlands.GaloisCohomology.localModule ι M ↑v) 1)) →
                            (real :
                                (w : { w // NumberField.InfinitePlace.IsReal w }) →
                                  AddSubgroup
                                    ↑(Langlands.ProfiniteCohomology.cohomology
                                        (Langlands.GaloisCohomology.realLocalModule ι M ↑w) 1)) →
                              motive { finite := finite, real := real }) →
                          motive t
@Langlands.GaloisCohomology.LocalConditions.ext : ∀ {K Ω : Type u} {inst : Field K} {inst_1 : NumberField K}
  {inst_2 : Field Ω} {inst_3 : Algebra K Ω} {inst_4 : IsSepClosure K Ω}
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω}
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  {inst_5 : Langlands.IsSmoothRep M} {x y : Langlands.GaloisCohomology.LocalConditions ι M},
  Langlands.GaloisCohomology.LocalConditions.finite x = Langlands.GaloisCohomology.LocalConditions.finite y →
    Langlands.GaloisCohomology.LocalConditions.real x = Langlands.GaloisCohomology.LocalConditions.real y → x = y
@Langlands.GaloisCohomology.LocalConditions.ext_iff : ∀ {K Ω : Type u} {inst : Field K} {inst_1 : NumberField K}
  {inst_2 : Field Ω} {inst_3 : Algebra K Ω} {inst_4 : IsSepClosure K Ω}
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω}
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  {inst_5 : Langlands.IsSmoothRep M} {x y : Langlands.GaloisCohomology.LocalConditions ι M},
  x = y ↔
    Langlands.GaloisCohomology.LocalConditions.finite x = Langlands.GaloisCohomology.LocalConditions.finite y ∧
      Langlands.GaloisCohomology.LocalConditions.real x = Langlands.GaloisCohomology.LocalConditions.real y
@Langlands.GaloisCohomology.LocalConditions.mk : {K Ω : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [inst_4 : IsSepClosure K Ω] →
            {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} →
              {ι : Langlands.Galois.PlaceEmbeddings K Ω} →
                {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} →
                  [inst_5 : Langlands.IsSmoothRep M] →
                    ((v : ↑S) →
                        AddSubgroup
                          ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.localModule ι M ↑v)
                              1)) →
                      ((w : { w // NumberField.InfinitePlace.IsReal w }) →
                          AddSubgroup
                            ↑(Langlands.ProfiniteCohomology.cohomology
                                (Langlands.GaloisCohomology.realLocalModule ι M ↑w) 1)) →
                        Langlands.GaloisCohomology.LocalConditions ι M
@Langlands.GaloisCohomology.LocalConditions.mk.noConfusion : {K Ω : Type u} →
  {inst : Field K} →
    {inst_1 : NumberField K} →
      {inst_2 : Field Ω} →
        {inst_3 : Algebra K Ω} →
          {inst_4 : IsSepClosure K Ω} →
            {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} →
              {ι : Langlands.Galois.PlaceEmbeddings K Ω} →
                {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} →
                  {inst_5 : Langlands.IsSmoothRep M} →
                    {P : Sort u_1} →
                      {finite :
                          (v : ↑S) →
                            AddSubgroup
                              ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.localModule ι M ↑v)
                                  1)} →
                        {real :
                            (w : { w // NumberField.InfinitePlace.IsReal w }) →
                              AddSubgroup
                                ↑(Langlands.ProfiniteCohomology.cohomology
                                    (Langlands.GaloisCohomology.realLocalModule ι M ↑w) 1)} →
                          {finite' :
                              (v : ↑S) →
                                AddSubgroup
                                  ↑(Langlands.ProfiniteCohomology.cohomology
                                      (Langlands.GaloisCohomology.localModule ι M ↑v) 1)} →
                            {real' :
                                (w : { w // NumberField.InfinitePlace.IsReal w }) →
                                  AddSubgroup
                                    ↑(Langlands.ProfiniteCohomology.cohomology
                                        (Langlands.GaloisCohomology.realLocalModule ι M ↑w) 1)} →
                              { finite := finite, real := real } = { finite := finite', real := real' } →
                                (finite ≍ finite' → real ≍ real' → P) → P
@Langlands.GaloisCohomology.LocalConditions.finite : {K Ω : Type u} →
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
                      (v : ↑S) →
                        AddSubgroup
                          ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.localModule ι M ↑v) 1)
@Langlands.GaloisCohomology.LocalConditions.real : {K Ω : Type u} →
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
                      (w : { w // NumberField.InfinitePlace.IsReal w }) →
                        AddSubgroup
                          ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.realLocalModule ι M ↑w)
                              1)
@Langlands.GaloisCohomology.LocalConditions.instPartialOrder : {K Ω : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [inst_4 : IsSepClosure K Ω] →
            {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} →
              {ι : Langlands.Galois.PlaceEmbeddings K Ω} →
                {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} →
                  [inst_5 : Langlands.IsSmoothRep M] → PartialOrder (Langlands.GaloisCohomology.LocalConditions ι M)
@Langlands.GaloisCohomology.LocalConditions.le_def : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω}
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_5 : Langlands.IsSmoothRep M] {L L' : Langlands.GaloisCohomology.LocalConditions ι M},
  L ≤ L' ↔
    (∀ (v : ↑S),
        Langlands.GaloisCohomology.LocalConditions.finite L v ≤
          Langlands.GaloisCohomology.LocalConditions.finite L' v) ∧
      ∀ (w : { w // NumberField.InfinitePlace.IsReal w }),
        Langlands.GaloisCohomology.LocalConditions.real L w ≤ Langlands.GaloisCohomology.LocalConditions.real L' w
@Langlands.GaloisCohomology.LocalConditions.instBot : {K Ω : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [inst_4 : IsSepClosure K Ω] →
            {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} →
              {ι : Langlands.Galois.PlaceEmbeddings K Ω} →
                {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} →
                  [inst_5 : Langlands.IsSmoothRep M] → Bot (Langlands.GaloisCohomology.LocalConditions ι M)
@Langlands.GaloisCohomology.LocalConditions.instTop : {K Ω : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [inst_4 : IsSepClosure K Ω] →
            {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} →
              {ι : Langlands.Galois.PlaceEmbeddings K Ω} →
                {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} →
                  [inst_5 : Langlands.IsSmoothRep M] → Top (Langlands.GaloisCohomology.LocalConditions ι M)
@Langlands.GaloisCohomology.LocalConditions.bot_finite : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω}
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_5 : Langlands.IsSmoothRep M] (v : ↑S), Langlands.GaloisCohomology.LocalConditions.finite ⊥ v = ⊥
@Langlands.GaloisCohomology.LocalConditions.bot_real : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω}
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_5 : Langlands.IsSmoothRep M] (w : { w // NumberField.InfinitePlace.IsReal w }),
  Langlands.GaloisCohomology.LocalConditions.real ⊥ w = ⊥
@Langlands.GaloisCohomology.LocalConditions.top_finite : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω}
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_5 : Langlands.IsSmoothRep M] (v : ↑S), Langlands.GaloisCohomology.LocalConditions.finite ⊤ v = ⊤
@Langlands.GaloisCohomology.LocalConditions.top_real : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω}
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_5 : Langlands.IsSmoothRep M] (w : { w // NumberField.InfinitePlace.IsReal w }),
  Langlands.GaloisCohomology.LocalConditions.real ⊤ w = ⊤
@Langlands.GaloisCohomology.LocalConditions.bot_le : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω}
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_5 : Langlands.IsSmoothRep M] (L : Langlands.GaloisCohomology.LocalConditions ι M), ⊥ ≤ L
@Langlands.GaloisCohomology.LocalConditions.le_top : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω}
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_5 : Langlands.IsSmoothRep M] (L : Langlands.GaloisCohomology.LocalConditions ι M), L ≤ ⊤
@Langlands.GaloisCohomology.LocalConditions.toLocalTerm : {K Ω : Type u} →
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
                      AddSubgroup (Langlands.GaloisCohomology.PoitouTate.LocalTerm ι M 1)
@Langlands.GaloisCohomology.LocalConditions.mem_toLocalTerm : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω}
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_5 : Langlands.IsSmoothRep M] {L : Langlands.GaloisCohomology.LocalConditions ι M}
  {ξ : Langlands.GaloisCohomology.PoitouTate.LocalTerm ι M 1},
  ξ ∈ Langlands.GaloisCohomology.LocalConditions.toLocalTerm L ↔
    (∀ (v : ↑S), Prod.fst ξ v ∈ Langlands.GaloisCohomology.LocalConditions.finite L v) ∧
      ∀ (w : { w // NumberField.InfinitePlace.IsReal w }),
        Prod.snd ξ w ∈ Langlands.GaloisCohomology.LocalConditions.real L w
@Langlands.GaloisCohomology.LocalConditions.toLocalTerm_mono : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω}
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_5 : Langlands.IsSmoothRep M] {L L' : Langlands.GaloisCohomology.LocalConditions ι M},
  L ≤ L' →
    Langlands.GaloisCohomology.LocalConditions.toLocalTerm L ≤ Langlands.GaloisCohomology.LocalConditions.toLocalTerm L'
@Langlands.GaloisCohomology.LocalConditions.toLocalTermEquiv : {K Ω : Type u} →
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
                      ↥(Langlands.GaloisCohomology.LocalConditions.toLocalTerm L) ≃
                        ((v : ↑S) → ↥(Langlands.GaloisCohomology.LocalConditions.finite L v)) ×
                          ((w : { w // NumberField.InfinitePlace.IsReal w }) →
                            ↥(Langlands.GaloisCohomology.LocalConditions.real L w))
@Langlands.GaloisCohomology.LocalConditions.card_toLocalTerm : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω}
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_5 : Langlands.IsSmoothRep M] [inst_6 : Finite ↑S] (L : Langlands.GaloisCohomology.LocalConditions ι M),
  Nat.card ↥(Langlands.GaloisCohomology.LocalConditions.toLocalTerm L) =
    (∏ v, Nat.card ↥(Langlands.GaloisCohomology.LocalConditions.finite L v)) *
      ∏ w, Nat.card ↥(Langlands.GaloisCohomology.LocalConditions.real L w)
@Langlands.GaloisCohomology.LocalConditions.toLocalTerm_bot : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω}
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_5 : Langlands.IsSmoothRep M], Langlands.GaloisCohomology.LocalConditions.toLocalTerm ⊥ = ⊥
@Langlands.GaloisCohomology.LocalConditions.toLocalTerm_top : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω}
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_5 : Langlands.IsSmoothRep M], Langlands.GaloisCohomology.LocalConditions.toLocalTerm ⊤ = ⊤
@Langlands.GaloisCohomology.LocalConditions.dual : {K Ω : Type u} →
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
                        Langlands.GaloisCohomology.LocalConditions ι M →
                          Langlands.GaloisCohomology.LocalConditions ι (Langlands.GaloisCohomology.PoitouTate.dual N M)
@Langlands.GaloisCohomology.LocalConditions.dual_finite : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} (N : ℕ)
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_5 : Langlands.IsSmoothRep M] [inst_6 : Finite ↑M] (L : Langlands.GaloisCohomology.LocalConditions ι M) (v : ↑S),
  Langlands.GaloisCohomology.LocalConditions.finite (Langlands.GaloisCohomology.LocalConditions.dual N L) v =
    Langlands.ProfiniteCohomology.rightOrthogonal (Langlands.GaloisCohomology.localPairing ι N M v)
      (Langlands.GaloisCohomology.LocalConditions.finite L v)
@Langlands.GaloisCohomology.LocalConditions.dual_real : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} (N : ℕ)
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_5 : Langlands.IsSmoothRep M] [inst_6 : Finite ↑M] (L : Langlands.GaloisCohomology.LocalConditions ι M)
  (w : { w // NumberField.InfinitePlace.IsReal w }),
  Langlands.GaloisCohomology.LocalConditions.real (Langlands.GaloisCohomology.LocalConditions.dual N L) w =
    Langlands.ProfiniteCohomology.rightOrthogonal (Langlands.GaloisCohomology.realLocalPairing ι N M w)
      (Langlands.GaloisCohomology.LocalConditions.real L w)
@Langlands.GaloisCohomology.LocalConditions.predual : {K Ω : Type u} →
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
                        Langlands.GaloisCohomology.LocalConditions ι (Langlands.GaloisCohomology.PoitouTate.dual N M) →
                          Langlands.GaloisCohomology.LocalConditions ι M
@Langlands.GaloisCohomology.LocalConditions.predual_finite : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} (N : ℕ)
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_5 : Langlands.IsSmoothRep M] [inst_6 : Finite ↑M]
  (L' : Langlands.GaloisCohomology.LocalConditions ι (Langlands.GaloisCohomology.PoitouTate.dual N M)) (v : ↑S),
  Langlands.GaloisCohomology.LocalConditions.finite (Langlands.GaloisCohomology.LocalConditions.predual N L') v =
    Langlands.ProfiniteCohomology.leftOrthogonal (Langlands.GaloisCohomology.localPairing ι N M v)
      (Langlands.GaloisCohomology.LocalConditions.finite L' v)
@Langlands.GaloisCohomology.LocalConditions.predual_real : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} (N : ℕ)
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_5 : Langlands.IsSmoothRep M] [inst_6 : Finite ↑M]
  (L' : Langlands.GaloisCohomology.LocalConditions ι (Langlands.GaloisCohomology.PoitouTate.dual N M))
  (w : { w // NumberField.InfinitePlace.IsReal w }),
  Langlands.GaloisCohomology.LocalConditions.real (Langlands.GaloisCohomology.LocalConditions.predual N L') w =
    Langlands.ProfiniteCohomology.leftOrthogonal (Langlands.GaloisCohomology.realLocalPairing ι N M w)
      (Langlands.GaloisCohomology.LocalConditions.real L' w)
@Langlands.GaloisCohomology.LocalConditions.dual_anti : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} (N : ℕ)
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_5 : Langlands.IsSmoothRep M] [inst_6 : Finite ↑M] {L L' : Langlands.GaloisCohomology.LocalConditions ι M},
  L ≤ L' → Langlands.GaloisCohomology.LocalConditions.dual N L' ≤ Langlands.GaloisCohomology.LocalConditions.dual N L
@Langlands.GaloisCohomology.LocalConditions.le_predual_dual : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} (N : ℕ)
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_5 : Langlands.IsSmoothRep M] [inst_6 : Finite ↑M] (L : Langlands.GaloisCohomology.LocalConditions ι M),
  L ≤ Langlands.GaloisCohomology.LocalConditions.predual N (Langlands.GaloisCohomology.LocalConditions.dual N L)
@Langlands.GaloisCohomology.LocalConditions.dual_bot : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} (N : ℕ)
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_5 : Langlands.IsSmoothRep M] [inst_6 : Finite ↑M], Langlands.GaloisCohomology.LocalConditions.dual N ⊥ = ⊤
@Langlands.GaloisCohomology.LocalConditions.toLocalTerm_dual : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} (N : ℕ)
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_5 : Langlands.IsSmoothRep M] [inst_6 : Finite ↑M] [inst_7 : Finite ↑S]
  (L : Langlands.GaloisCohomology.LocalConditions ι M),
  Langlands.GaloisCohomology.LocalConditions.toLocalTerm (Langlands.GaloisCohomology.LocalConditions.dual N L) =
    Langlands.ProfiniteCohomology.rightOrthogonal (Langlands.GaloisCohomology.localTermPairing ι N M)
      (Langlands.GaloisCohomology.LocalConditions.toLocalTerm L)
@Langlands.GaloisCohomology.LocalConditions.toLocalTerm_predual : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} (N : ℕ)
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_5 : Langlands.IsSmoothRep M] [inst_6 : Finite ↑M] [inst_7 : Finite ↑S]
  (L' : Langlands.GaloisCohomology.LocalConditions ι (Langlands.GaloisCohomology.PoitouTate.dual N M)),
  Langlands.GaloisCohomology.LocalConditions.toLocalTerm (Langlands.GaloisCohomology.LocalConditions.predual N L') =
    Langlands.ProfiniteCohomology.leftOrthogonal (Langlands.GaloisCohomology.localTermPairing ι N M)
      (Langlands.GaloisCohomology.LocalConditions.toLocalTerm L')
@Langlands.GaloisCohomology.LocalConditions.predual_dual : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} (N : ℕ) [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_6 : Langlands.IsSmoothRep M] [inst_7 : Finite ↑M],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ↑N ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S) →
    (∀ (m : ↑M), N • m = 0) →
      ∀ (L : Langlands.GaloisCohomology.LocalConditions ι M),
        Langlands.GaloisCohomology.LocalConditions.predual N (Langlands.GaloisCohomology.LocalConditions.dual N L) = L
@Langlands.GaloisCohomology.LocalConditions.dual_predual : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} (N : ℕ) [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_6 : Langlands.IsSmoothRep M] [inst_7 : Finite ↑M],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ↑N ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S) →
    (∀ (m : ↑M), N • m = 0) →
      ∀ (L' : Langlands.GaloisCohomology.LocalConditions ι (Langlands.GaloisCohomology.PoitouTate.dual N M)),
        Langlands.GaloisCohomology.LocalConditions.dual N (Langlands.GaloisCohomology.LocalConditions.predual N L') = L'
@Langlands.GaloisCohomology.LocalConditions.card_finite_mul_card_dual_finite : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} (N : ℕ) [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_6 : Langlands.IsSmoothRep M] [inst_7 : Finite ↑M],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ↑N ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S) →
    (∀ (m : ↑M), N • m = 0) →
      ∀ (L : Langlands.GaloisCohomology.LocalConditions ι M) (v : ↑S),
        Nat.card ↥(Langlands.GaloisCohomology.LocalConditions.finite L v) *
            Nat.card
              ↥(Langlands.GaloisCohomology.LocalConditions.finite (Langlands.GaloisCohomology.LocalConditions.dual N L)
                  v) =
          Nat.card ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.localModule ι M ↑v) 1)
@Langlands.GaloisCohomology.LocalConditions.card_real_mul_card_dual_real : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} (N : ℕ) [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_6 : Langlands.IsSmoothRep M] [inst_7 : Finite ↑M],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ↑N ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S) →
    (∀ (m : ↑M), N • m = 0) →
      ∀ (L : Langlands.GaloisCohomology.LocalConditions ι M) (w : { w // NumberField.InfinitePlace.IsReal w }),
        Nat.card ↥(Langlands.GaloisCohomology.LocalConditions.real L w) *
            Nat.card
              ↥(Langlands.GaloisCohomology.LocalConditions.real (Langlands.GaloisCohomology.LocalConditions.dual N L)
                  w) =
          Nat.card ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.realLocalModule ι M ↑w) 1)
@Langlands.GaloisCohomology.LocalConditions.dual_top : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} (N : ℕ) [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_6 : Langlands.IsSmoothRep M] [inst_7 : Finite ↑M],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ↑N ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S) →
    (∀ (m : ↑M), N • m = 0) → Langlands.GaloisCohomology.LocalConditions.dual N ⊤ = ⊥
```

## Outline of the proofs

Everything is the general theory of `Langlands.GaloisCohomology.Global.Selmer.Orthogonal` applied to
the local pairings, whose perfectness is `bijective_localPairing`, `bijective_localPairing_flip`,
`bijective_realLocalPairing`, `bijective_realLocalPairing_flip` of
`Langlands.GaloisCohomology.Global.Selmer.LocalPairing`; the product statements are
`rightOrthogonal_prodPairing_prod` and `rightOrthogonal_piPairing_pi` (and their left forms). The
local cohomology groups are finite by `finite_cohomology_localModule` and
`finite_cohomology_realLocalModule`.

## Declarations

`LocalConditions`, `LocalConditions.casesOn`, `LocalConditions.noConfusion`, `LocalConditions.rec`, `LocalConditions.recOn`, `LocalConditions.ext`, `LocalConditions.ext_iff`, `LocalConditions.mk`, `LocalConditions.mk.noConfusion`, `LocalConditions.finite`, `LocalConditions.real`, `LocalConditions.instPartialOrder`, `LocalConditions.le_def`, `LocalConditions.instBot`, `LocalConditions.instTop`, `LocalConditions.bot_finite`, `LocalConditions.bot_real`, `LocalConditions.top_finite`, `LocalConditions.top_real`, `LocalConditions.bot_le`, `LocalConditions.le_top`, `LocalConditions.toLocalTerm`, `LocalConditions.mem_toLocalTerm`, `LocalConditions.toLocalTerm_mono`, `LocalConditions.toLocalTermEquiv`, `LocalConditions.card_toLocalTerm`, `LocalConditions.toLocalTerm_bot`, `LocalConditions.toLocalTerm_top`, `LocalConditions.dual`, `LocalConditions.dual_finite`, `LocalConditions.dual_real`, `LocalConditions.predual`, `LocalConditions.predual_finite`, `LocalConditions.predual_real`, `LocalConditions.dual_anti`, `LocalConditions.le_predual_dual`, `LocalConditions.dual_bot`, `LocalConditions.toLocalTerm_dual`, `LocalConditions.toLocalTerm_predual`, `LocalConditions.predual_dual`, `LocalConditions.dual_predual`, `LocalConditions.card_finite_mul_card_dual_finite`, `LocalConditions.card_real_mul_card_dual_real`, `LocalConditions.dual_top`.

## References

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed. (Springer 2008, corrected printing 2013), (8.7.8) (collections of local conditions and their orthogonal complements `L^D`), p. 511.
