# The infinite places of a subfield of `K_S` as double cosets

`Langlands/GaloisCohomology/Global/EulerCharacteristic/Internal/InducedPlaces.lean`, namespace `Langlands.GaloisCohomology`.

Let `K` be a number field, `Ω` a Galois extension, `S` a set of finite places of `K`, `G_S` the Galois
group of the maximal extension `K_S ⊆ Ω` unramified outside `S`, `ι : PlaceEmbeddings K Ω`, and `L` a
number field with `K → L → Ω` and `L ⊆ K_S`; let `U ⊆ G_S` be the open subgroup fixing `L`. For a
real place `v` of `K` let `G_v = Gal(K̄_v/K_v)` (of order two) with its localization
`φ_v : G_v → G_S`.

To `x ∈ G_S` this file attaches the embedding `ι_v ∘ x⁻¹` of `L` into `K̄_v` (`infiniteEmbedding`), the
complex embedding of `L` obtained from it through `K̄_v ≅ ℂ` (`complexEmbeddingAt`), and the infinite
place of `L` it defines. This depends only on the double coset `U x G_v` (`mackeyInfinitePlace`), and

* the double cosets `U \ G_S / G_v` correspond bijectively to the infinite places of `L` above `v`
  (`mackeyInfinitePlace_injective`, `exists_mackeyInfinitePlace_eq`, `comap_mackeyInfinitePlace`);
* the place attached to `U x G_v` is real exactly when the Mackey subgroup `G_v ∩ x⁻¹ U x` is all of
  `G_v` (`mackeySubgroup_eq_top_iff_isReal`); otherwise it is trivial
  (`mackeySubgroup_eq_bot_of_ne_top`);
* for such a real place `w` and any embeddings `ιL : PlaceEmbeddings L Ω`, the image of complex
  conjugation of `G_v` under `y ↦ x φ_v(y) x⁻¹`, transported to `G_{S_L}(L)`, is conjugate to the image
  of complex conjugation of `L_w` under the localization of `ιL`
  (`exists_conj_realLocalizationHom_closureConj`).

These are the facts about the real places that Shapiro's lemma for the Euler characteristic ratio
needs (`Langlands.GaloisCohomology.Global.EulerCharacteristic.Induced`).

```lean
theorem exists_conj_realLocalizationHom_closureConj (v : {v : InfinitePlace K // v.IsReal})
    (x : GaloisGroupUnramifiedOutside K Ω S)
    (hw : (InfinitePlace.mk (complexEmbeddingAt hL ι v.1 x)).IsReal)
    (hc : x * realLocalizationHom ι S v.1 (closureConj v.1 v.2) * x⁻¹ ∈ fixingOpenSubgroup S hL) :
    ∃ g : GaloisGroupUnramifiedOutside L Ω (finitePlacesAbove L S),
      realLocalizationHom ιL (finitePlacesAbove L S) (InfinitePlace.mk (complexEmbeddingAt hL ι v.1 x))
          (closureConj _ hw) =
        g⁻¹ * fixingOpenSubgroupEquiv S hL ⟨_, hc⟩ * g
```

## Complete types

In the `#check @c` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.exists_conj_realLocalizationHom_closureConj : ∀ {K L Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field L] [inst_3 : NumberField L] [inst_4 : Field Ω] [inst_5 : Algebra K L]
  [inst_6 : Algebra K Ω] [inst_7 : Algebra L Ω] [inst_8 : IsScalarTower K L Ω] [inst_9 : IsGalois K Ω]
  [inst_10 : IsGalois L Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (ιL : Langlands.Galois.PlaceEmbeddings L Ω)
  (v : { v : NumberField.InfinitePlace K // v.IsReal }) (x : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)
  (hw : (NumberField.InfinitePlace.mk (Langlands.GaloisCohomology.complexEmbeddingAt hL ι (↑v) x)).IsReal)
  (hc :
    x * (Langlands.Galois.realLocalizationHom ι S ↑v) (Langlands.GaloisCohomology.closureConj ↑v ⋯) * x⁻¹ ∈
      Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL),
  ∃ (g : Langlands.Galois.GaloisGroupUnramifiedOutside L Ω (Langlands.Galois.finitePlacesAbove L S)),
    (Langlands.Galois.realLocalizationHom ιL (Langlands.Galois.finitePlacesAbove L S)
          (NumberField.InfinitePlace.mk (Langlands.GaloisCohomology.complexEmbeddingAt hL ι (↑v) x)))
        (Langlands.GaloisCohomology.closureConj
          (NumberField.InfinitePlace.mk (Langlands.GaloisCohomology.complexEmbeddingAt hL ι (↑v) x)) hw) =
      g⁻¹ *
          (Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroupEquiv S hL)
            ⟨x * (Langlands.Galois.realLocalizationHom ι S ↑v) (Langlands.GaloisCohomology.closureConj ↑v ⋯) * x⁻¹,
              hc⟩ *
        g
```

## Outline of the proofs

The embedding `ι_v ∘ x⁻¹` restricted to `L` changes by an automorphism of `K̄_v` when `x` is multiplied by `G_v` on the right and is unchanged when `x` is multiplied by `U` on the left; the resulting map from double cosets to the places of `L` above `v` is injective by the uniqueness of extensions up to `G_v` and surjective because every embedding of `L` over `K` extends to `Ω`. The Mackey subgroup `{y ∈ G_v | x φ_v(y) x⁻¹ ∈ U}` is all of `G_v` exactly when complex conjugation fixes the image of `L`, i.e. when the place is real.

- `exists_conj_realLocalizationHom_closureConj`: **Complex conjugations correspond.** Let `v` be a real place of `K` and `x ∈ G_S` such that the place `w` of `L` attached to `x` is real. Then the image of complex conjugation of `G_v` under `y ↦ x φ_v(y) x⁻¹`, transported to `G_{S_L}(L)`, is conjugate there to the image of complex conjugation of `L_w` under the localization of `ιL`.

## Declarations

`infiniteEmbedding`, `infiniteEmbedding_apply`, `mem_mackeySubgroup_infinite_iff`, `infiniteEmbedding_mul`, `mem_fixingOpenSubgroup_of_infiniteEmbedding_eq`, `exists_infiniteEmbedding_eq`, `complexEmbeddingAt`, `complexEmbeddingAt_apply`, `complexEmbeddingAt_comp_algebraMap`, `complexEmbeddingAt_mul`, `mackeyInfinitePlace`, `mackeyInfinitePlace_mk`, `comap_mackeyInfinitePlace`, `complexEmbeddingAt_eq_of_mk_eq`, `mackeyInfinitePlace_injective`, `exists_mackeyInfinitePlace_eq`, `mackeySubgroup_eq_bot_of_ne_top`, `mackeySubgroup_eq_top_iff_isReal`, `eq_of_comp_eq`, `exists_conj_realLocalizationHom_closureConj`.

## References

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed. (Springer 2008, corrected printing 2013), proof of (8.7.4), p. 507 (the decomposition of H⁰(G_p, Ind A) over the double cosets G_p \ G_S / U at a real place p).
