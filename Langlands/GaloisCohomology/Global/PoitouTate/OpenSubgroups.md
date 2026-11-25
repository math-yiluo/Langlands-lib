# Open subgroups of `G_S` and their fixed fields

`Langlands/GaloisCohomology/Global/PoitouTate/OpenSubgroups.lean`, namespace `Langlands.GaloisCohomology.PoitouTate`.

Let `L ⊆ K_S` be a finite extension of `K`, `U ⊆ G_S` the open subgroup fixing it and
`S_L` the places of `L` above `S`. The isomorphism `U ≅ G_{S_L}(L)` (`fixingOpenSubgroupEquiv`)
matches the Mackey family of local groups of `U` (indexed by the double cosets
`U \ G_S / G_{K_v}`, `v ∈ S`) with the localizations of `G_{S_L}(L)` at the places of `S_L`
(`mackeyPlaceEquiv`, `fixingOpenSubgroupEquiv_mackeyConj_eq_localizationHom`) for the embeddings
`placeEmbeddingsOver hL ι ι₀` of `Ω` at the places of `L` (those of the Mackey correspondence above
`S`, those of `ι₀` elsewhere), and `μ_N(L_{S_L})` with `μ_N(K_S)` (`dualizingModuleResIso`). So the
cohomology with compact support of `G_{S_L}(L)` with coefficients `μ_N` is that of `U` with its
Mackey family (`mackeyCompactTransport`), compatibly with cup products with `ℤ/N`
(`compactTransport_compactCupRes` of `Langlands.GaloisCohomology.CompactSupport.Transport`).

Consequence (`bijective_compactZmodDualityMap_fixingOpenSubgroup`): if the duality for `ℤ/N` with
compact support holds for `G_{S_L}(L)` with a trace generating `Hom(H_c³(G_{S_L}(L), μ_N), ℤ/N)`, it
holds for `U` with every surjective trace, since the two traces then differ by a unit
(`isUnit_of_surjective_of_eq_mul` of `Langlands.Cohomology.Profinite.Duality.DualModule`, `bijective_compactZmodDualityMap_of_transport`).

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.PoitouTate.bijective_compactZmodDualityMap_fixingOpenSubgroup.{u} {K L Ω : Type u} [Field K]
  [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
  [IsGalois K Ω] [IsGalois L Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (ι₀ : Langlands.Galois.PlaceEmbeddings L Ω) (N : ℕ)
  [hDU :
    Langlands.IsSmoothRep
      (Rep.res (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype
        (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N))]
  {r s : ℕ} (h : r + s = 3)
  (T' :
    ↑(Langlands.GaloisCohomology.compactSupportCohomologyRes
          (Langlands.GaloisCohomology.PoitouTate.localFamily
            (Langlands.GaloisCohomology.PoitouTate.placeEmbeddingsOver hL ι ι₀)
            (Langlands.Galois.finitePlacesAbove L S))
          (Langlands.GaloisCohomology.PoitouTate.dualizingModule L Ω (Langlands.Galois.finitePlacesAbove L S) N) 3) →+
      ZMod N)
  (hgen :
    ∀
      (χ :
        ↑(Langlands.GaloisCohomology.compactSupportCohomologyRes
              (Langlands.GaloisCohomology.PoitouTate.localFamily
                (Langlands.GaloisCohomology.PoitouTate.placeEmbeddingsOver hL ι ι₀)
                (Langlands.Galois.finitePlacesAbove L S))
              (Langlands.GaloisCohomology.PoitouTate.dualizingModule L Ω (Langlands.Galois.finitePlacesAbove L S) N)
              3) →+
          ZMod N),
      ∃ c,
        ∀
          (y :
            ↑(Langlands.GaloisCohomology.compactSupportCohomologyRes
                (Langlands.GaloisCohomology.PoitouTate.localFamily
                  (Langlands.GaloisCohomology.PoitouTate.placeEmbeddingsOver hL ι ι₀)
                  (Langlands.Galois.finitePlacesAbove L S))
                (Langlands.GaloisCohomology.PoitouTate.dualizingModule L Ω (Langlands.Galois.finitePlacesAbove L S) N)
                3)),
          χ y = c * T' y)
  (hbij :
    Function.Bijective
      ⇑(Langlands.GaloisCohomology.compactZmodDualityMap
          (Langlands.GaloisCohomology.PoitouTate.localFamily
            (Langlands.GaloisCohomology.PoitouTate.placeEmbeddingsOver hL ι ι₀)
            (Langlands.Galois.finitePlacesAbove L S))
          (Langlands.GaloisCohomology.PoitouTate.dualizingModule L Ω (Langlands.Galois.finitePlacesAbove L S) N) ⋯ T'
          h))
  (T :
    ↑(Langlands.GaloisCohomology.compactSupportCohomologyRes
          (Langlands.GaloisCohomology.mackeyFamily
            (Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)
            (Langlands.GaloisCohomology.PoitouTate.localFamily ι S))
          (Rep.res (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype
            (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N))
          3) →+
      ZMod N)
  (hT : Function.Surjective ⇑T) :
  Function.Bijective
    ⇑(Langlands.GaloisCohomology.compactZmodDualityMap
        (Langlands.GaloisCohomology.mackeyFamily (Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)
          (Langlands.GaloisCohomology.PoitouTate.localFamily ι S))
        (Rep.res (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype
          (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N))
        ⋯ T h)
Langlands.GaloisCohomology.PoitouTate.bijective_compactZmodDualityMap_of_transport.{u} {G G' : Type u} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] {ι ι' : Type u}
  {H : ι → Type u} {H' : ι' → Type u} [(i : ι) → Group (H i)] [(i : ι) → TopologicalSpace (H i)]
  [∀ (i : ι), IsTopologicalGroup (H i)] [(j : ι') → Group (H' j)] [(j : ι') → TopologicalSpace (H' j)]
  [∀ (j : ι'), IsTopologicalGroup (H' j)] (φ : (i : ι) → H i →ₜ* G) (φ' : (j : ι') → H' j →ₜ* G') (θ : G ≃ₜ* G')
  (e : ι ≃ ι') (ψ : (i : ι) → H i ≃ₜ* H' (e i)) (hcomm : ∀ (i : ι) (h : H i), θ ((φ i) h) = (φ' (e i)) ((ψ i) h))
  {n : ℕ} {D' : Rep.{u, u, u} (ULift.{u, 0} ℤ) G'} [Langlands.IsSmoothRep D'] {D : Rep.{u, u, u} (ULift.{u, 0} ℤ) G}
  [Langlands.IsSmoothRep D] (hD' : ∀ (d : ↑D'), n • d = 0) (hD : ∀ (d : ↑D), n • d = 0) (f : Rep.res (↑θ) D' ≅ D)
  {r s : ℕ} (h : r + s = 3) (T' : ↑(Langlands.GaloisCohomology.compactSupportCohomologyRes φ' D' 3) →+ ZMod n)
  (T : ↑(Langlands.GaloisCohomology.compactSupportCohomologyRes φ D 3) →+ ZMod n) (c : ZMod n) (hc : IsUnit c)
  (hT :
    ∀ (w : ↑(Langlands.GaloisCohomology.compactSupportCohomologyRes φ' D' 3)),
      T ((ModuleCat.Hom.hom (Langlands.GaloisCohomology.compactTransport φ φ' θ e ψ hcomm f.hom 3)) w) = c * T' w)
  (hbij : Function.Bijective ⇑(Langlands.GaloisCohomology.compactZmodDualityMap φ' D' hD' T' h)) :
  Function.Bijective ⇑(Langlands.GaloisCohomology.compactZmodDualityMap φ D hD T h)
Langlands.GaloisCohomology.PoitouTate.dualizingModuleResIso.{u} {K L Ω : Type u} [Field K] [NumberField K] [Field L]
  [NumberField L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) (N : ℕ) :
  Rep.res (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroupEquiv S hL))
      (Langlands.GaloisCohomology.PoitouTate.dualizingModule L Ω (Langlands.Galois.finitePlacesAbove L S) N) ≅
    Rep.res (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype
      (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N)
Langlands.GaloisCohomology.PoitouTate.fixingOpenSubgroupEquiv_mackeyConj_eq_localizationHom.{u} {K L Ω : Type u}
  [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω]
  [IsScalarTower K L Ω] [IsGalois K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) [IsGalois L Ω] (ι₀ : Langlands.Galois.PlaceEmbeddings L Ω)
  (p :
    (v : ↑S) ×
      Langlands.ProfiniteCohomology.MackeyDoubleCoset
        (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL))
        (Langlands.Galois.localizationHom ι S ↑v).toMonoidHom)
  (σ :
    ↥(Langlands.ProfiniteCohomology.mackeySubgroup
        (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL))
        (Langlands.Galois.localizationHom ι S ↑p.fst).toMonoidHom (Quotient.out p.snd))) :
  (Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroupEquiv S hL)
      ((Langlands.ProfiniteCohomology.mackeyConj
          (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL))
          (Langlands.Galois.localizationHom ι S ↑p.fst).toMonoidHom (Quotient.out p.snd))
        σ) =
    (Langlands.Galois.localizationHom (Langlands.GaloisCohomology.PoitouTate.placeEmbeddingsOver hL ι ι₀)
        (Langlands.Galois.finitePlacesAbove L S) ↑((Langlands.Galois.mackeyPlaceEquiv S hL ι) p))
      ((Langlands.Galois.mackeyLocalEquiv hL ι (↑p.fst) (Quotient.out p.snd)) σ)
Langlands.GaloisCohomology.PoitouTate.mackeyCompactTransport.{u} {K L Ω : Type u} [Field K] [NumberField K] [Field L]
  [NumberField L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  [IsGalois L Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (ι₀ : Langlands.Galois.PlaceEmbeddings L Ω) (N : ℕ)
  [hDU :
    Langlands.IsSmoothRep
      (Rep.res (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype
        (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N))]
  (n : ℕ) :
  Langlands.GaloisCohomology.compactSupportCohomologyRes
      (Langlands.GaloisCohomology.PoitouTate.localFamily
        (Langlands.GaloisCohomology.PoitouTate.placeEmbeddingsOver hL ι ι₀) (Langlands.Galois.finitePlacesAbove L S))
      (Langlands.GaloisCohomology.PoitouTate.dualizingModule L Ω (Langlands.Galois.finitePlacesAbove L S) N) n ≅
    Langlands.GaloisCohomology.compactSupportCohomologyRes
      (Langlands.GaloisCohomology.mackeyFamily (Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)
        (Langlands.GaloisCohomology.PoitouTate.localFamily ι S))
      (Rep.res (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype
        (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N))
      n
Langlands.GaloisCohomology.PoitouTate.mackeyEmbedding.{u} {K L Ω : Type u} [Field K] [NumberField K] [Field L]
  [NumberField L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (w : ↑(Langlands.Galois.finitePlacesAbove L S)) :
  Ω →ₐ[L] AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion L ↑w)
Langlands.GaloisCohomology.PoitouTate.mackeyEmbedding_mackeyPlaceEquiv.{u} {K L Ω : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (p :
    (v : ↑S) ×
      Langlands.ProfiniteCohomology.MackeyDoubleCoset
        (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL))
        (Langlands.Galois.localizationHom ι S ↑v).toMonoidHom) :
  Langlands.GaloisCohomology.PoitouTate.mackeyEmbedding hL ι ((Langlands.Galois.mackeyPlaceEquiv S hL ι) p) =
    Langlands.Galois.localEmbeddingOver hL ι (↑p.fst) (Quotient.out p.snd)
Langlands.GaloisCohomology.PoitouTate.maximalUnramifiedOutsideEquiv_symm_apply_apply.{u} {K L Ω : Type u} [Field K]
  [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
  [IsGalois K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (σ : ↥↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL))
  (y : ↥(Langlands.Galois.maximalUnramifiedOutside L Ω (Langlands.Galois.finitePlacesAbove L S))) :
  (Langlands.Galois.maximalUnramifiedOutsideEquiv hL).symm
      (((Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroupEquiv S hL) σ) y) =
    ↑σ ((Langlands.Galois.maximalUnramifiedOutsideEquiv hL).symm y)
Langlands.GaloisCohomology.PoitouTate.placeEmbeddingsOver.{u} {K L Ω : Type u} [Field K] [NumberField K] [Field L]
  [NumberField L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (ι₀ : Langlands.Galois.PlaceEmbeddings L Ω) :
  Langlands.Galois.PlaceEmbeddings L Ω
Langlands.GaloisCohomology.PoitouTate.placeEmbeddingsOver_finite.{u} {K L Ω : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (ι₀ : Langlands.Galois.PlaceEmbeddings L Ω)
  (w : ↑(Langlands.Galois.finitePlacesAbove L S)) :
  (Langlands.GaloisCohomology.PoitouTate.placeEmbeddingsOver hL ι ι₀).finite ↑w =
    Langlands.GaloisCohomology.PoitouTate.mackeyEmbedding hL ι w
```

## Outline of the proofs

`placeEmbeddingsOver` is built with `Equiv.piCongrLeft` along `mackeyPlaceEquiv`; the compatibility with the Mackey conjugations is `fixingOpenSubgroupEquiv_mackeyConj` of the Library. The cup product compatibility is `compactTransport_compactCupRes` with `zmodMulPairingRight_res` of the module `Langlands.GaloisCohomology.CompactSupport.DualityMap`; a surjective trace is a unit multiple of a generating one (`isUnit_of_surjective_of_eq_mul` of the module `Langlands.Cohomology.Profinite.Duality.DualModule`, where also `zmodRepResIso`, the identification of `ℤ/n` restricted along an isomorphism, is), and multiplying the trace by a unit preserves bijectivity (`bijective_of_transport` of the module `Langlands.Cohomology.Profinite.Duality.Devissage`).

## Declarations

`bijective_compactZmodDualityMap_of_transport`, `mackeyEmbedding`, `mackeyEmbedding_mackeyPlaceEquiv`, `placeEmbeddingsOver`, `placeEmbeddingsOver_finite`, `fixingOpenSubgroupEquiv_mackeyConj_eq_localizationHom`, `maximalUnramifiedOutsideEquiv_symm_apply_apply`, `dualizingModuleResIso`, `mackeyCompactTransport`, `bijective_compactZmodDualityMap_fixingOpenSubgroup`.

## References

- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter I, §4, Theorem 4.10, pp. 56–57; chapter II, §2, pp. 165–166 (cohomology with compact support).
