# The Kummer sequence of `G_S` over a subgroup `G_S(L)`

`Langlands/GaloisCohomology/Global/EulerCharacteristic/Internal/BaseKummer.lean`, namespace `Langlands.GaloisCohomology`.

Let `K` be a number field, `Ω` a separable closure, `S` a finite set of finite places of `K`, and
`L ⊆ K_S` finite Galois over `K`, with `P ⊆ G_S` the subgroup fixing `L`. The cohomology groups
`Aᵢ = Hⁱ(P, 𝒪_Sˣ)` of the `S`-units of `K_S` are `Gal(L/K)`-modules by conjugation. This file
identifies `A₀` with the `S`-units of `L` as a `Gal(L/K)`-module (`sUnitsOfEquivCohomologyZero`,
`sUnitsOfEquivCohomologyZero_smul`), shows that `A₁` is finite (it embeds into the `S_L`-class group
of `L`, `finite_cohomology_one_res_maximalSUnits`), and records the properties of `μ_ℓ` needed for the
coprime twist: `P` acts trivially on it when `μ_ℓ ⊆ L` (`rootsOfUnity_res_trivial`), and it has
dimension one over `𝔽_ℓ` (`finrank_zmodRepOfTorsion_rootsOfUnity`).

```lean
theorem map_mem_maximalSUnits_iff {x : Lˣ} :
    Units.map (embeddingMaximalUnramifiedOutside hL : L →* maximalUnramifiedOutside K Ω S) x ∈
      maximalSUnits K Ω S ↔ x ∈ sUnitsOf S L
def sUnitsOfToInvariants :
    Additive (sUnitsOf S L) →+ (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (maximalSUnitsModule K Ω S)).ρ.invariants
def sUnitsOfEquivCohomologyZero :
    Additive (sUnitsOf S L) ≃+ cohomology (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (maximalSUnitsModule K Ω S)) 0
theorem sUnitsOfEquivCohomologyZero_smul [(GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).Normal]
    (σ : GaloisGroupUnramifiedOutside K Ω S) (x : Additive (sUnitsOf S L)) :
    (letI
def resMaximalSUnitsHom :
    Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroupEquiv S hL).symm.toMulEquiv.toMonoidHom
      (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (maximalSUnitsModule K Ω S)) ⟶
      maximalSUnitsModule L Ω (finitePlacesAbove L S)
theorem finite_cohomology_one_res_maximalSUnits :
    Finite (cohomology (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (maximalSUnitsModule K Ω S)) 1)
```

## Complete types

In the `#check @c` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.map_mem_maximalSUnits_iff : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {L : Type u} [inst_5 : Field L]
  [inst_6 : NumberField L] [inst_7 : Algebra K L] [inst_8 : Algebra L Ω] [inst_9 : IsScalarTower K L Ω]
  (hL : ∀ (x : L), (algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) {x : Lˣ},
  (Units.map ↑(Langlands.Galois.embeddingMaximalUnramifiedOutside hL)) x ∈
      Langlands.GaloisCohomology.maximalSUnits K Ω S ↔
    x ∈ Langlands.GaloisCohomology.sUnitsOf S L
@Langlands.GaloisCohomology.sUnitsOfToInvariants : {K Ω : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [inst_4 : IsSepClosure K Ω] →
            {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} →
              {L : Type u} →
                [inst_5 : Field L] →
                  [inst_6 : NumberField L] →
                    [inst_7 : Algebra K L] →
                      [inst_8 : Algebra L Ω] →
                        [inst_9 : IsScalarTower K L Ω] →
                          (hL : ∀ (x : L), (algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) →
                            Additive ↥(Langlands.GaloisCohomology.sUnitsOf S L) →+
                              ↥(Rep.res
                                      (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype
                                      (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S)).ρ.invariants
@Langlands.GaloisCohomology.sUnitsOfEquivCohomologyZero : {K Ω : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [inst_4 : IsSepClosure K Ω] →
            {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} →
              {L : Type u} →
                [inst_5 : Field L] →
                  [inst_6 : NumberField L] →
                    [inst_7 : Algebra K L] →
                      [inst_8 : Algebra L Ω] →
                        [inst_9 : IsScalarTower K L Ω] →
                          (hL : ∀ (x : L), (algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) →
                            Additive ↥(Langlands.GaloisCohomology.sUnitsOf S L) ≃+
                              ↑(Langlands.ProfiniteCohomology.cohomology
                                  (Rep.res
                                    (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype
                                    (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S))
                                  0)
@Langlands.GaloisCohomology.sUnitsOfEquivCohomologyZero_smul : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {L : Type u} [inst_5 : Field L]
  [inst_6 : NumberField L] [inst_7 : Algebra K L] [inst_8 : Algebra L Ω] [inst_9 : IsScalarTower K L Ω]
  (hL : ∀ (x : L), (algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) [inst_10 : IsGalois K L]
  [inst_11 : (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).Normal]
  (σ : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) (x : Additive ↥(Langlands.GaloisCohomology.sUnitsOf S L)),
  (Langlands.GaloisCohomology.sUnitsOfEquivCohomologyZero hL) ((Langlands.Galois.galRestrict hL) σ • x) =
    (ModuleCat.Hom.hom
        (Langlands.ProfiniteCohomology.cohomologyConj (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S)
          (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)) 0 σ))
      ((Langlands.GaloisCohomology.sUnitsOfEquivCohomologyZero hL) x)
@Langlands.GaloisCohomology.resMaximalSUnitsHom : {K Ω : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [inst_4 : IsSepClosure K Ω] →
            {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} →
              {L : Type u} →
                [inst_5 : Field L] →
                  [inst_6 : NumberField L] →
                    [inst_7 : Algebra K L] →
                      [inst_8 : Algebra L Ω] →
                        [inst_9 : IsScalarTower K L Ω] →
                          (hL : ∀ (x : L), (algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) →
                            Rep.res
                                (Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroupEquiv S
                                      hL).symm.toMonoidHom
                                (Rep.res
                                  (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype
                                  (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S)) ⟶
                              Langlands.GaloisCohomology.maximalSUnitsModule L Ω
                                (Langlands.Galois.finitePlacesAbove L S)
@Langlands.GaloisCohomology.finite_cohomology_one_res_maximalSUnits : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {L : Type u} [inst_5 : Field L]
  [inst_6 : NumberField L] [inst_7 : Algebra K L] [inst_8 : Algebra L Ω] [inst_9 : IsScalarTower K L Ω]
  (hL : ∀ (x : L), (algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S),
  Finite
    ↑(Langlands.ProfiniteCohomology.cohomology
        (Rep.res (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype
          (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S))
        1)
```

## Outline of the proofs

`H⁰(P, 𝒪_Sˣ)` is the group of `G_S(L)`-invariant `S`-units of `K_S`, i.e. the `S_L`-units of `L`, equivariantly for `Gal(L/K)`; `H¹(P, 𝒪_Sˣ)` embeds into the `S_L`-class group of `L` (Hilbert 90 and the divisor sequence, transported along `P ≅ G_{S_L}(L)`), hence is finite.

- `map_mem_maximalSUnits_iff`: A unit of `L` is an `S`-unit of `K_S` exactly when it is an `S`-unit of `L`.
- `sUnitsOfToInvariants`: The `S`-units of `L` as `P`-invariants of the `S`-units of `K_S`.
- `sUnitsOfEquivCohomologyZero`: `H⁰(P, 𝒪_Sˣ)` is the group of `S`-units of `L`.
- `sUnitsOfEquivCohomologyZero_smul`: The identification of `H⁰(P, 𝒪_Sˣ)` with the `S`-units of `L` is `Gal(L/K)`-equivariant.
- `resMaximalSUnitsHom`: The `S`-units of `K_S` restricted to `P ≅ G_{S_L}(L)` are the `S_L`-units of `L_{S_L} = K_S`.
- `finite_cohomology_one_res_maximalSUnits`: `H¹(P, 𝒪_Sˣ)` is finite: it is `H¹(G_{S_L}(L), 𝒪_{S_L}ˣ)`, which embeds into the `S_L`-class group of `L`.

## Declarations

`map_mem_maximalSUnits_iff`, `maximalSUnitsVal`, `isSmoothRep_res_maximalSUnitsModule`, `sUnitsOfToInvariants`, `coe_sUnitsOfToInvariants_apply`, `sUnitsOfToInvariants_bijective`, `sUnitsOfEquivCohomologyZero`, `embedding_galRestrict_smul`, `sUnitsOfEquivCohomologyZero_smul`, `resMaximalSUnitsHom`, `resMaximalSUnitsHom_bijective`, `finite_cohomology_one_res_maximalSUnits`, `rootsOfUnity_res_trivial`, `finrank_zmodRepOfTorsion_rootsOfUnity`.

## References

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed. (Springer 2008, corrected printing 2013), proof of (8.7.4), p. 506 ((i) and (ii): H⁰ and H¹ of μ_p over K through the S-units).
