# Characters of `G_S` at the places outside `S`: inertia and Frobenius

`Langlands/GaloisCohomology/Global/Abelianization/Frobenius.lean`, namespace
`Langlands.GaloisCohomology`.

For a number field `K` (`K : Type u`), a separable closure `Ω` (`Ω : Type v`), a finite set `S` of
finite places and `n ≠ 0`, a continuous character `χ : G_S → ℤ/n` is described at a finite place
`v ∉ S` in the Library's local vocabulary of `Langlands.GaloisRepresentation` (the absolute Galois
group `LocalGroup v` of `K_v`, its inertia group `localInertia v`, the predicate
`IsGeometricFrobeniusLift v`, and `localToGlobalGalois v`, Mathlib's `Field.absoluteGaloisGroup.map`
for the completion). An element of `Gal(AlgebraicClosure K / K)` is carried to `Gal(Ω / K)` by an
arbitrary isomorphism `f : AlgebraicClosure K ≃ₐ[K] Ω`; the values of `χ` do not depend on `f`
(`apply_quotientMap_autCongr_eq`).

* **Inertia** (`apply_quotientMap_autCongr_localToGlobalGalois_of_mem_localInertia`): `χ` is `1` on
  the image of `localInertia v`.
* **Frobenius** (`continuousCharEquivNarrowSIdeleClass_finiteIdeleInclusion_of_isGeometricFrobeniusLift`,
  `continuousCharEquivSIdeleClass_finiteIdeleInclusion_of_isGeometricFrobeniusLift`): for a
  uniformizer `π` of `K_v` and a geometric Frobenius lift `g` at `v`, the character
  `continuousCharEquivNarrowSIdeleClass Ω hS n χ` of the narrow `S`-idèle class group takes at the
  class of `π` the value of `χ` at the image of `g`; likewise for `continuousCharEquivSIdeleClass`.
  On the presentation of the module `Langlands.GaloisCohomology.Global.Abelianization.Presentation`,
  the generator of the divisors prime to `S` at `v` goes to the value at a geometric Frobenius
  (`continuousCharEquivSIdeleClass_sPresentation_one_single`).

Behind both is `matchesGeometricArtinOutside_absoluteCharacter`: for `Ω = AlgebraicClosure K`,
`χ` read on the absolute Galois group satisfies the Library's `MatchesGeometricArtinOutside` for
the idèle-class character `ideleClassCharacter χ` (the continuous character `x ↦ χ(σ|_{K_S})` of
`IdeleClasses K`, `σ` lifting `geometricArtinMap K x`).

## Complete types

```lean
@Langlands.GaloisCohomology.apply_quotientMap_autCongr_eq : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K] {Ω : Type v} [inst_2 : Field Ω] [inst_3 : Algebra K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {n : ℕ} [inst_4 : IsGalois K Ω]
  (χ : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S →ₜ* Multiplicative (ZMod n))
  (f f' : AlgebraicClosure K ≃ₐ[K] Ω) (τ : Gal(AlgebraicClosure K/K)),
  χ ((Langlands.Galois.GaloisGroupUnramifiedOutside.quotientMap K Ω S) (f.autCongr τ)) =
    χ ((Langlands.Galois.GaloisGroupUnramifiedOutside.quotientMap K Ω S) (f'.autCongr τ))

@Langlands.GaloisCohomology.ideleClassCharacter : {K : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} →
        {n : ℕ} →
          (Langlands.Galois.GaloisGroupUnramifiedOutside K (AlgebraicClosure K) S →ₜ* Multiplicative (ZMod n)) →
            Langlands.Global.IdeleClasses K →ₜ* Multiplicative (ZMod n)

@Langlands.GaloisCohomology.ideleClassCharacter_ideleClassMap : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {n : ℕ} [inst_2 : NeZero n]
  (χ : Langlands.Galois.GaloisGroupUnramifiedOutside K (AlgebraicClosure K) S →ₜ* Multiplicative (ZMod n))
  (x : Langlands.Global.Ideles K),
  (Langlands.GaloisCohomology.ideleClassCharacter χ) ((Langlands.Global.ideleClassMap K) x) =
    (Langlands.GaloisCohomology.narrowSIdeleClassCharacter χ)
      ((Langlands.GaloisCohomology.NarrowSIdeleClassGroup.mk S) x)

@Langlands.GaloisCohomology.matchesGeometricArtinOutside_absoluteCharacter : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {n : ℕ} [NeZero n] (hS : S.Finite)
  (χ : Langlands.Galois.GaloisGroupUnramifiedOutside K (AlgebraicClosure K) S →ₜ* Multiplicative (ZMod n)),
  Langlands.GaloisRepresentation.MatchesGeometricArtinOutside hS.toFinset
    (Langlands.GaloisCohomology.ideleClassCharacter χ)
    (have this := Langlands.GaloisCohomology.absoluteCharacter χ;
    this)

@Langlands.GaloisCohomology.absoluteCharacter_continuousCharCongr : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K] {Ω : Type v} [inst_2 : Field Ω] [inst_3 : Algebra K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {n : ℕ} [inst_4 : IsSepClosure K Ω]
  (χ : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S →ₜ* Multiplicative (ZMod n)) (f : AlgebraicClosure K ≃ₐ[K] Ω)
  (τ : Gal(AlgebraicClosure K/K)),
  (Langlands.GaloisCohomology.absoluteCharacter
        ((Langlands.GaloisCohomology.continuousCharCongr
            (Langlands.Galois.galoisGroupUnramifiedOutsideCongr S
              (IsSepClosure.equiv K (AlgebraicClosure K) Ω))
            n)
          χ))
      τ =
    χ ((Langlands.Galois.GaloisGroupUnramifiedOutside.quotientMap K Ω S) (f.autCongr τ))

@Langlands.GaloisCohomology.apply_quotientMap_autCongr_localToGlobalGalois_of_mem_localInertia : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K] {Ω : Type v} [inst_2 : Field Ω] [inst_3 : Algebra K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {n : ℕ} [NeZero n]
  [inst_5 : IsSepClosure K Ω],
  S.Finite →
    ∀ (χ : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S →ₜ* Multiplicative (ZMod n))
      (f : AlgebraicClosure K ≃ₐ[K] Ω) {v : Langlands.Global.FinitePlace K},
      v ∉ S →
        ∀ (i : ↥(Langlands.GaloisRepresentation.localInertia v)),
          χ
              ((Langlands.Galois.GaloisGroupUnramifiedOutside.quotientMap K Ω S)
                (f.autCongr ((Langlands.GaloisRepresentation.localToGlobalGalois v) ↑i))) =
            1

@Langlands.GaloisCohomology.continuousCharEquivNarrowSIdeleClass_finiteIdeleInclusion_of_isGeometricFrobeniusLift : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K] {Ω : Type v} [inst_2 : Field Ω] [inst_3 : Algebra K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {n : ℕ} [inst_4 : NeZero n]
  [inst_5 : IsSepClosure K Ω] (hS : S.Finite)
  (χ : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S →ₜ* Multiplicative (ZMod n)) (f : AlgebraicClosure K ≃ₐ[K] Ω)
  {v : Langlands.Global.FinitePlace K},
  v ∉ S →
    ∀ (π : (Langlands.Global.FiniteCompletion K v)ˣ),
      Valued.v ↑π = WithZero.exp (-1) →
        ∀ (g : Langlands.GaloisRepresentation.LocalGroup v),
          Langlands.GaloisRepresentation.IsGeometricFrobeniusLift v g →
            ((Langlands.GaloisCohomology.continuousCharEquivNarrowSIdeleClass Ω hS n) χ)
                ((Langlands.GaloisCohomology.NarrowSIdeleClassGroup.mk S)
                  ((Langlands.Global.finiteIdeleInclusion K v) π)) =
              χ
                ((Langlands.Galois.GaloisGroupUnramifiedOutside.quotientMap K Ω S)
                  (f.autCongr ((Langlands.GaloisRepresentation.localToGlobalGalois v) g)))

@Langlands.GaloisCohomology.continuousCharEquivSIdeleClass_finiteIdeleInclusion_of_isGeometricFrobeniusLift : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K] {Ω : Type v} [inst_2 : Field Ω] [inst_3 : Algebra K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {n : ℕ} [inst_4 : NeZero n]
  [inst_5 : IsSepClosure K Ω] (hS : S.Finite) (h : Odd n ∨ NumberField.IsTotallyComplex K)
  (χ : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S →ₜ* Multiplicative (ZMod n)) (f : AlgebraicClosure K ≃ₐ[K] Ω)
  {v : Langlands.Global.FinitePlace K},
  v ∉ S →
    ∀ (π : (Langlands.Global.FiniteCompletion K v)ˣ),
      Valued.v ↑π = WithZero.exp (-1) →
        ∀ (g : Langlands.GaloisRepresentation.LocalGroup v),
          Langlands.GaloisRepresentation.IsGeometricFrobeniusLift v g →
            ((Langlands.GaloisCohomology.continuousCharEquivSIdeleClass Ω hS h) χ)
                ((Langlands.GaloisCohomology.SIdeleClassGroup.mk S) ((Langlands.Global.finiteIdeleInclusion K v) π)) =
              χ
                ((Langlands.Galois.GaloisGroupUnramifiedOutside.quotientMap K Ω S)
                  (f.autCongr ((Langlands.GaloisRepresentation.localToGlobalGalois v) g)))

@Langlands.GaloisCohomology.continuousCharEquivSIdeleClass_sPresentation_one_single : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K] {Ω : Type v} [inst_2 : Field Ω] [inst_3 : Algebra K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {n : ℕ} [inst_4 : NeZero n]
  [inst_5 : IsSepClosure K Ω] [inst_6 : Finite ↑S] (h : Odd n ∨ NumberField.IsTotallyComplex K)
  (χ : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S →ₜ* Multiplicative (ZMod n)) (f : AlgebraicClosure K ≃ₐ[K] Ω)
  {v : Langlands.Global.FinitePlace K} (hv : v ∉ S) (g : Langlands.GaloisRepresentation.LocalGroup v),
  Langlands.GaloisRepresentation.IsGeometricFrobeniusLift v g →
    ((Langlands.GaloisCohomology.continuousCharEquivSIdeleClass Ω ⋯ h) χ)
        ((Langlands.GaloisCohomology.sPresentation S) (1, Multiplicative.ofAdd fun₀ | ⟨v, hv⟩ => 1)) =
      χ
        ((Langlands.Galois.GaloisGroupUnramifiedOutside.quotientMap K Ω S)
          (f.autCongr ((Langlands.GaloisRepresentation.localToGlobalGalois v) g)))
```

## Outline of the proofs

`ideleClassCharacter χ` is trivial on the integral local units outside `S`
(`ideleCharacter_finiteIdeleInclusion` of the module `Langlands.GaloisCohomology.Global.Abelianization`).
By `exists_matchesGeometricArtinOutside` (module `Langlands.Galois.FiniteHeckeAvatarLiftProof`,
with the Library's theorems `finiteAbelianClassFieldExistence`, `finiteArtinUnramifiedCriterion`
and `finiteUnramifiedGaloisRestriction`) it has a lift `ψ` to the absolute Galois group that is
trivial on inertia outside `S` and sends geometric Frobenius lifts to the values at uniformizers.
`MatchesGeometricArtinOutside.apply_eq_of_geometricArtinMap` gives `ψ σ = ideleClassCharacter χ x`
whenever `σ` lifts `geometricArtinMap K x`, and that is also `χ(σ|_{K_S})`; as the Artin map is
surjective, `ψ` is `χ` read on the absolute Galois group. For a general `Ω` the character is
transported as in `continuousCharEquivNarrowSIdeleClass` (`absoluteCharacter_continuousCharCongr`).

## Declarations

In the order of the file:

- `apply_quotientMap_autCongr_eq` (theorem): The value of a character of `G_S` on the restriction of an automorphism of `AlgebraicClosure K` carried to `Ω` by an isomorphism does not depend on the isomorphism.
- `ideleClassCharacter` (def): The idèle-class character attached to a continuous character of `G_S(AlgebraicClosure K)`, as a continuous homomorphism.
- `ideleClassCharacter_ideleClassMap` (theorem): On the class of an idèle, `ideleClassCharacter χ` is `narrowSIdeleClassCharacter χ`.
- `matchesGeometricArtinOutside_absoluteCharacter` (theorem): A continuous character of `G_S(AlgebraicClosure K)`, read on the absolute Galois group, matches its idèle-class character outside `S` in the sense of `MatchesGeometricArtinOutside`: it is trivial on local inertia at every finite place outside `S`, and its value at a geometric Frobenius lift is the value of the idèle-class character at a uniformizer. By uniqueness of the lift (`exists_matchesGeometricArtinOutside`, `MatchesGeometricArtinOutside.unique`, `MatchesGeometricArtinOutside.apply_eq_of_geometricArtinMap`).
- `absoluteCharacter_continuousCharCongr` (theorem): A continuous character of `G_S(Ω)`, transported to `G_S(AlgebraicClosure K)` as in `continuousCharEquivNarrowSIdeleClass`, read on `Gal(AlgebraicClosure K / K)`: it is the character on `Gal(Ω / K)` carried by any isomorphism `f : AlgebraicClosure K ≃ₐ[K] Ω`.
- `apply_quotientMap_autCongr_localToGlobalGalois_of_mem_localInertia` (theorem): **Inertia.** For finite `S`, a continuous character of `G_S` with values in `ℤ/n` is trivial on the image of the local inertia group at every finite place outside `S` (the local Galois group of `K_v` mapped to `Gal(AlgebraicClosure K / K)` by Mathlib's `Field.absoluteGaloisGroup.map`, then to `Gal(Ω / K)` by any isomorphism `f`).
- `continuousCharEquivNarrowSIdeleClass_finiteIdeleInclusion_of_isGeometricFrobeniusLift` (theorem): **Frobenius.** For finite `S`, a finite place `v ∉ S`, a uniformizer `π` of `K_v` and a geometric Frobenius lift `g` at `v`, the character of the narrow `S`-idèle class group attached to a continuous character `χ` of `G_S` takes at the class of `π` the value of `χ` at the image of `g`.
- `continuousCharEquivSIdeleClass_finiteIdeleInclusion_of_isGeometricFrobeniusLift` (theorem): **Frobenius**, for `continuousCharEquivSIdeleClass`.
- `continuousCharEquivSIdeleClass_sPresentation_one_single` (theorem): **Frobenius**, on the presentation of the `S`-idèle class group: the generator of the divisors prime to `S` at `v ∉ S` corresponds to a geometric Frobenius at `v`.

## References

- J. Neukirch, *Algebraic Number Theory* (Springer, 1999), Chapter VI, Proposition (5.6), p. 391
  (compatibility of the global norm residue symbol with the local ones).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition, corrected
  printing (Springer, 2013), Chapter VIII, §3, p. 460 (the local group at `p` goes onto the
  decomposition group, the units onto the inertia group).
