# The places of `L` above `S` as a `Gal(L/K)`-set

`Langlands/GaloisCohomology/Global/EulerCharacteristic/Internal/PlaceOrbits.lean`, namespace `Langlands.GaloisCohomology`.

Let `L ⊆ K_S` be finite Galois over the number field `K`, with group `Γ = Gal(L/K)` acting on the
places of `L` by transport of structure (`finitePlaceAction`). For an embedding `j : L → K̄_v`, the
place of `L` defined by `j ∘ σ⁻¹` is `σ` applied to the place defined by `j`
(`placeOfAlgHom_comp_inv`): the completion `L_{σw}` is carried to `L_w` by `σ⁻¹`
(`finiteCompletionAlgEquiv`). Hence, with `w_v` the place of `L` given by the chosen embedding
`ι_v` of `K_S` into `K̄_v`:

* the places of `L` above `v` form one orbit, that of `w_v` (`exists_galRestrict_smul_eq`);
* the stabilizer of `w_v` is the decomposition group `D_v`, the image of the local Galois group
  `Gal(K̄_v/K_v) → G_S → Γ` (`smul_basePlace_eq_iff`);

so that the places above `S` are `⊔_{v ∈ S} Γ/D_v` as a `Γ`-set (`placesAboveEquiv`).

```lean
theorem placeOfAlgHom_comp_inv (j : L →ₐ[K] AlgebraicClosure (v.adicCompletion K)) (σ : L ≃ₐ[K] L) :
    ((placeOfAlgHom (j.comp ((σ⁻¹ : L ≃ₐ[K] L) : L →ₐ[K] L))).1 : HeightOneSpectrum (𝓞 L)) =
      σ • (placeOfAlgHom j).1
theorem smul_basePlace_eq_iff (v : HeightOneSpectrum (𝓞 K)) (τ : L ≃ₐ[K] L) :
    τ • ((basePlace hL ι v).1 : HeightOneSpectrum (𝓞 L)) = (basePlace hL ι v).1 ↔
      τ ∈ decompositionGroup hL ι v
```

## Complete types

In the `#check @c` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.placeOfAlgHom_comp_inv : ∀ {K L : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field L] [inst_3 : NumberField L] [inst_4 : Algebra K L]
  {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
  (j : L →ₐ[K] AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) (σ : Gal(L/K)),
  ↑(Langlands.Galois.placeOfAlgHom (j.comp ↑σ⁻¹)) = σ • ↑(Langlands.Galois.placeOfAlgHom j)
@Langlands.GaloisCohomology.smul_basePlace_eq_iff : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {L : Type u} [inst_5 : Field L]
  [inst_6 : NumberField L] [inst_7 : Algebra K L] [inst_8 : Algebra L Ω] [inst_9 : IsScalarTower K L Ω]
  (hL : ∀ (x : L), (algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) [inst_10 : IsGalois K L]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (τ : Gal(L/K)),
  τ • ↑(Langlands.GaloisCohomology.basePlace hL ι v) = ↑(Langlands.GaloisCohomology.basePlace hL ι v) ↔
    τ ∈ Langlands.GaloisCohomology.decompositionGroup hL ι v
```

## Outline of the proofs

The places of `L` above `v` form one `Gal(L/K)`-orbit; the stabilizer of the place given by `ι_v` is the image of `G_{K_v}` (the decomposition group), since `σ` fixes the place exactly when `ι_v ∘ σ⁻¹` and `ι_v` differ by an automorphism of `K̄_v` (`placeOfAlgHom`, `finiteCompletionAlgEquiv`).

- `placeOfAlgHom_comp_inv`: **Conjugate places.** The place of `L` defined by `j ∘ σ⁻¹` is `σ` applied to the place defined by `j`.
- `smul_basePlace_eq_iff`: **The stabilizer of the base place is the decomposition group.**

## Declarations

`liesOver_smul`, `placeOfAlgHom_comp_inv`, `localEmbedding_mul_left`, `localPlace_mul_left`, `basePlace`, `decompositionGroup`, `exists_galRestrict_smul_eq`, `smul_basePlace_eq_iff`.

## References

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed. (Springer 2008, corrected printing 2013), proof of (8.7.4), p. 506 (the permutation modules ⊕_{P ∈ S(K)} F_p).
