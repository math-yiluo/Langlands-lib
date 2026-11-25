# The group `G_S` in two isomorphic extensions

`Langlands/Galois/RestrictedRamification/ClosureChange.lean`, namespace `Langlands.Galois`.

For a number field `K` (`K : Type u`), a set `S` of finite places of `K` and an isomorphism
`e : Ω ≃ₐ[K] Ω'` of extensions of `K` (`Ω : Type v`, `Ω' : Type w`), this file compares the groups
`G_S = Gal(K_S / K)` of `Langlands.Galois.GaloisGroupUnramifiedOutside` formed in `Ω` and in `Ω'`;
this is how a statement proved for `AlgebraicClosure K` is carried to any separable closure.

* **Unramifiedness along isomorphisms.** A prime `P` of an `R`-algebra `B` is unramified over `R` if
  its preimage under an `R`-algebra isomorphism `A ≃ₐ[R] B` is (`isUnramifiedAt_of_algEquiv`); so a
  prime of `R` unramified in `A` is unramified in `B` (`isUnramifiedIn_of_algEquiv`). Applied to the
  rings of integers of `E` and of its image, `e` carries a finite subextension unramified outside
  `S` to one unramified outside `S` (`isUnramifiedOutside_map_algEquiv`), and, for Galois
  extensions, carries `K_S ⊆ Ω` onto `K_S ⊆ Ω'` (`maximalUnramifiedOutside_map_algEquiv`,
  `maximalUnramifiedOutsideAlgEquiv`).
* **Krull topology.** Conjugation by `e` carries the fixing subgroup of an intermediate field to
  the fixing subgroup of its image (`fixingSubgroup_map_autCongr`) and is continuous
  (`continuous_autCongr`); `autCongrContinuous e : (Ω₁ ≃ₐ[B] Ω₁) ≃ₜ* (Ω₂ ≃ₐ[B] Ω₂)`.
* **`G_S`.** `galoisGroupUnramifiedOutsideCongr S e : G_S(Ω) ≃ₜ* G_S(Ω')` is conjugation by the
  restriction of `e`; it is compatible with the quotient maps from `Gal(Ω / K)` and `Gal(Ω' / K)`
  (`galoisGroupUnramifiedOutsideCongr_quotientMap`).

## Complete types

```lean
@Langlands.Galois.isUnramifiedAt_of_algEquiv : ∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : CommRing B]
  [inst_3 : Algebra R A] [inst_4 : Algebra R B] (ψ : A ≃ₐ[R] B) (P : Ideal B) [inst_5 : P.IsPrime]
  [Algebra.IsUnramifiedAt R (Ideal.comap ψ P)], Algebra.IsUnramifiedAt R P

@Langlands.Galois.isUnramifiedIn_of_algEquiv : ∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : CommRing B]
  [inst_3 : Algebra R A] [inst_4 : Algebra R B] (ψ : A ≃ₐ[R] B) {p : Ideal R},
  Algebra.IsUnramifiedIn A p → Algebra.IsUnramifiedIn B p

@Langlands.Galois.isUnramifiedOutside_map_algEquiv : ∀ {K : Type u} [inst : Field K] [NumberField K] {Ω : Type v} {Ω' : Type w} [inst_2 : Field Ω] [inst_3 : Field Ω']
  [inst_4 : Algebra K Ω] [inst_5 : Algebra K Ω']
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (e : Ω ≃ₐ[K] Ω')
  {E : IntermediateField K Ω} [FiniteDimensional K ↥E],
  Langlands.Galois.IsUnramifiedOutside S E → Langlands.Galois.IsUnramifiedOutside S (IntermediateField.map (↑e) E)

@Langlands.Galois.maximalUnramifiedOutside_map_algEquiv : ∀ {K : Type u} [inst : Field K] [NumberField K] {Ω : Type v} {Ω' : Type w} [inst_2 : Field Ω] [inst_3 : Field Ω']
  [inst_4 : Algebra K Ω] [inst_5 : Algebra K Ω']
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [IsGalois K Ω] [IsGalois K Ω']
  (e : Ω ≃ₐ[K] Ω'),
  IntermediateField.map (↑e) (Langlands.Galois.maximalUnramifiedOutside K Ω S) =
    Langlands.Galois.maximalUnramifiedOutside K Ω' S

@Langlands.Galois.fixingSubgroup_map_autCongr : ∀ {B : Type u_1} {Ω₁ : Type u_2} {Ω₂ : Type u_3} [inst : Field B] [inst_1 : Field Ω₁] [inst_2 : Field Ω₂]
  [inst_3 : Algebra B Ω₁] [inst_4 : Algebra B Ω₂] (e : Ω₁ ≃ₐ[B] Ω₂) (F : IntermediateField B Ω₁),
  Subgroup.map e.autCongr.toMonoidHom F.fixingSubgroup = (IntermediateField.map (↑e) F).fixingSubgroup

@Langlands.Galois.continuous_autCongr : ∀ {B : Type u_1} {Ω₁ : Type u_2} {Ω₂ : Type u_3} [inst : Field B] [inst_1 : Field Ω₁] [inst_2 : Field Ω₂]
  [inst_3 : Algebra B Ω₁] [inst_4 : Algebra B Ω₂] (e : Ω₁ ≃ₐ[B] Ω₂), Continuous ⇑e.autCongr

@Langlands.Galois.autCongrContinuous : {B : Type u_1} →
  {Ω₁ : Type u_2} →
    {Ω₂ : Type u_3} →
      [inst : Field B] →
        [inst_1 : Field Ω₁] →
          [inst_2 : Field Ω₂] →
            [inst_3 : Algebra B Ω₁] → [inst_4 : Algebra B Ω₂] → (Ω₁ ≃ₐ[B] Ω₂) → Gal(Ω₁/B) ≃ₜ* Gal(Ω₂/B)

@Langlands.Galois.autCongrContinuous_apply : ∀ {B : Type u_1} {Ω₁ : Type u_2} {Ω₂ : Type u_3} [inst : Field B] [inst_1 : Field Ω₁] [inst_2 : Field Ω₂]
  [inst_3 : Algebra B Ω₁] [inst_4 : Algebra B Ω₂] (e : Ω₁ ≃ₐ[B] Ω₂) (σ : Gal(Ω₁/B)) (x : Ω₂),
  ((Langlands.Galois.autCongrContinuous e) σ) x = e (σ (e.symm x))

@Langlands.Galois.maximalUnramifiedOutsideAlgEquiv : {K : Type u} →
  [inst : Field K] →
    [NumberField K] →
      {Ω : Type v} →
        {Ω' : Type w} →
          [inst_2 : Field Ω] →
            [inst_3 : Field Ω'] →
              [inst_4 : Algebra K Ω] →
                [inst_5 : Algebra K Ω'] →
                  [IsGalois K Ω] →
                    [IsGalois K Ω'] →
                      (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
                        (Ω ≃ₐ[K] Ω') →
                          ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S) ≃ₐ[K]
                            ↥(Langlands.Galois.maximalUnramifiedOutside K Ω' S)

@Langlands.Galois.maximalUnramifiedOutsideAlgEquiv_apply : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K] {Ω : Type v} {Ω' : Type w} [inst_2 : Field Ω]
  [inst_3 : Field Ω'] [inst_4 : Algebra K Ω] [inst_5 : Algebra K Ω'] [inst_6 : IsGalois K Ω] [inst_7 : IsGalois K Ω']
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (e : Ω ≃ₐ[K] Ω')
  (x : ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)),
  ↑((Langlands.Galois.maximalUnramifiedOutsideAlgEquiv S e) x) = e ↑x

@Langlands.Galois.maximalUnramifiedOutsideAlgEquiv_symm_apply : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K] {Ω : Type v} {Ω' : Type w} [inst_2 : Field Ω]
  [inst_3 : Field Ω'] [inst_4 : Algebra K Ω] [inst_5 : Algebra K Ω'] [inst_6 : IsGalois K Ω] [inst_7 : IsGalois K Ω']
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (e : Ω ≃ₐ[K] Ω')
  (x : ↥(Langlands.Galois.maximalUnramifiedOutside K Ω' S)),
  ↑((Langlands.Galois.maximalUnramifiedOutsideAlgEquiv S e).symm x) = e.symm ↑x

@Langlands.Galois.galoisGroupUnramifiedOutsideCongr : {K : Type u} →
  [inst : Field K] →
    [NumberField K] →
      {Ω : Type v} →
        {Ω' : Type w} →
          [inst_2 : Field Ω] →
            [inst_3 : Field Ω'] →
              [inst_4 : Algebra K Ω] →
                [inst_5 : Algebra K Ω'] →
                  [IsGalois K Ω] →
                    [IsGalois K Ω'] →
                      (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
                        (Ω ≃ₐ[K] Ω') →
                          Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S ≃ₜ*
                            Langlands.Galois.GaloisGroupUnramifiedOutside K Ω' S

@Langlands.Galois.galoisGroupUnramifiedOutsideCongr_apply : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K] {Ω : Type v} {Ω' : Type w} [inst_2 : Field Ω]
  [inst_3 : Field Ω'] [inst_4 : Algebra K Ω] [inst_5 : Algebra K Ω'] [inst_6 : IsGalois K Ω] [inst_7 : IsGalois K Ω']
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (e : Ω ≃ₐ[K] Ω')
  (σ : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) (x : ↥(Langlands.Galois.maximalUnramifiedOutside K Ω' S)),
  ↑(((Langlands.Galois.galoisGroupUnramifiedOutsideCongr S e) σ) x) =
    e ↑(σ ((Langlands.Galois.maximalUnramifiedOutsideAlgEquiv S e).symm x))

@Langlands.Galois.galoisGroupUnramifiedOutsideCongr_quotientMap : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K] {Ω : Type v} {Ω' : Type w} [inst_2 : Field Ω]
  [inst_3 : Field Ω'] [inst_4 : Algebra K Ω] [inst_5 : Algebra K Ω'] [inst_6 : IsGalois K Ω] [inst_7 : IsGalois K Ω']
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (e : Ω ≃ₐ[K] Ω') (σ : Gal(Ω/K)),
  (Langlands.Galois.galoisGroupUnramifiedOutsideCongr S e)
      ((Langlands.Galois.GaloisGroupUnramifiedOutside.quotientMap K Ω S) σ) =
    (Langlands.Galois.GaloisGroupUnramifiedOutside.quotientMap K Ω' S) (e.autCongr σ)
```

## Outline of the proofs

* `isUnramifiedAt_of_algEquiv`: make `B` an `A`-algebra through the isomorphism. Then `B` is
  formally unramified over `A` (a surjection, `Algebra.FormallyUnramified.of_surjective`), so is
  its localization at `P` (`Algebra.FormallyUnramified.comp`), i.e. `P` is unramified over `A`;
  `Algebra.IsUnramifiedAt.comp` composes this with unramifiedness of the preimage of `P` over `R`.
* `maximalUnramifiedOutside_map_algEquiv`: by `mem_maximalUnramifiedOutside_iff`, an element of
  `K_S` lies in a finite subextension unramified outside `S`, whose image under `e` (or `e⁻¹`) is
  again one.
* `continuous_autCongr`: a homomorphism of topological groups is continuous if it is continuous at
  `1`; a neighbourhood of `1` in the Krull topology contains the fixing subgroup of a finite
  subextension `D`, and conjugation by `e` carries the fixing subgroup of `e⁻¹(D)` into it.

The two lemmas on `autCongr` are also stated, with the same proofs, in the Library's module
`Langlands.LocalFactor.Ramification.Wintenberger.APF`, which depends on the FontaineWintenberger
copy; they are restated here so that this file depends on Mathlib and on the module
`Langlands.Galois.RestrictedRamification.MaximalExtension` only.

## Declarations

In the order of the file:

- `isUnramifiedAt_of_algEquiv` (theorem): A prime `P` of `B` is unramified over `R` if its preimage under an isomorphism of `R`-algebras `A ≃ₐ[R] B` is.
- `isUnramifiedIn_of_algEquiv` (theorem): A prime of `R` is unramified in `B` if it is unramified in an `R`-algebra isomorphic to `B`.
- `isUnramifiedOutside_map_algEquiv` (theorem): An isomorphism of extensions carries a finite subextension unramified outside `S` to one unramified outside `S`.
- `maximalUnramifiedOutside_map_algEquiv` (theorem): An isomorphism of Galois extensions carries the maximal extension unramified outside `S` onto the maximal extension unramified outside `S`.
- `fixingSubgroup_map_autCongr` (theorem): Conjugation by an isomorphism of extensions carries the fixing subgroup of an intermediate field to the fixing subgroup of its image.
- `continuous_autCongr` (theorem): Conjugation by an isomorphism of extensions is continuous for the Krull topologies.
- `autCongrContinuous` (def): Conjugation by an isomorphism of extensions, as an isomorphism of topological groups for the Krull topologies.
- `autCongrContinuous_apply` (theorem): The value of `autCongrContinuous e σ`: `e ∘ σ ∘ e⁻¹`.
- `maximalUnramifiedOutsideAlgEquiv` (def): The isomorphism of the maximal extensions unramified outside `S` induced by an isomorphism `e : Ω ≃ₐ[K] Ω'`.
- `maximalUnramifiedOutsideAlgEquiv_apply` (theorem): `maximalUnramifiedOutsideAlgEquiv S e` is `e` on elements.
- `maximalUnramifiedOutsideAlgEquiv_symm_apply` (theorem): Its inverse is `e⁻¹` on elements.
- `galoisGroupUnramifiedOutsideCongr` (def): An isomorphism `e : Ω ≃ₐ[K] Ω'` of Galois extensions induces, by conjugation, an isomorphism of topological groups `G_S(Ω) ≃ₜ* G_S(Ω')`.
- `galoisGroupUnramifiedOutsideCongr_apply` (theorem): The value of `galoisGroupUnramifiedOutsideCongr S e σ` on an element of `K_S ⊆ Ω'`.
- `galoisGroupUnramifiedOutsideCongr_quotientMap` (theorem): The isomorphism `G_S(Ω) ≃ₜ* G_S(Ω')` is compatible with the quotient maps from `Gal(Ω / K)` and `Gal(Ω' / K)` and conjugation by `e`.

## References

None beyond the definitions of the module `Langlands.Galois.RestrictedRamification.MaximalExtension`.
