# Characters of `G_S` and the `S`-idèle class group

`Langlands/GaloisCohomology/Global/Abelianization.lean`, namespace `Langlands.GaloisCohomology`.

**Main theorem.** Let `K` be a number field (`K : Type u`), `Ω` a separable closure of `K`
(`Ω : Type v`, `[IsSepClosure K Ω]`; an algebraic closure is one, `K` having characteristic `0`),
`S` a finite set of finite places of `K` and `n ≠ 0`. Then the continuous characters of
`G_S = Gal(K_S / K)` (`Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S`, `K_S` the maximal
extension of `K` in `Ω` unramified at the finite places outside `S`, the real places allowed to
ramify) with values in `ℤ/n` correspond to the homomorphisms from the narrow `S`-idèle class group
`I_K / K^× U^S_+` to `ℤ/n`:

```lean
continuousCharEquivNarrowSIdeleClass Ω (hS : S.Finite) (n : ℕ) [NeZero n] :
    ContinuousMonoidHom (GaloisGroupUnramifiedOutside K Ω S) (Multiplicative (ZMod n)) ≃*
      (NarrowSIdeleClassGroup S →* Multiplicative (ZMod n))
```

There is no condition on `n` and none on the real places. If `n` is odd or `K` is totally complex,
the homomorphisms from the narrow group to `ℤ/n` are those from the `S`-idèle class group
`I_K / K^× U^S` (`NarrowSIdeleClassGroup.precompToSIdeleClassGroupEquiv`), which gives

```lean
continuousCharEquivSIdeleClass Ω (hS : S.Finite) [NeZero n] (h : Odd n ∨ IsTotallyComplex K) :
    ContinuousMonoidHom (GaloisGroupUnramifiedOutside K Ω S) (Multiplicative (ZMod n)) ≃*
      (SIdeleClassGroup S →* Multiplicative (ZMod n))
```

Without the condition the second form fails in general: a real place may ramify in `K_S`, and a
character of order `2` may then be nontrivial on complex conjugation there, while every
homomorphism from `SIdeleClassGroup S` kills the archimedean components. The groups are those of
the module `Langlands.GaloisCohomology.Global.Abelianization.SIdeleClassGroup`.

**Normalization.** The isomorphisms are built with the Library's global Artin map
`Langlands.ClassFieldTheory.Global.Artin.geometricArtinMap K : IdeleClasses K →ₜ*
Field.absoluteGaloisGroupAbelianization K`, which is in the geometric normalization (a uniformizer
at an unramified place goes to the inverse of the arithmetic Frobenius). The character of the
idèles attached to `χ` is `x ↦ χ(σ|_{K_S})` for any `σ ∈ Gal(Ω / K)` whose conjugate into
`AlgebraicClosure K`, by any isomorphism `e : Ω ≃ₐ[K] AlgebraicClosure K`, has image
`geometricArtinMap K x` in the abelianization (`continuousCharEquivNarrowSIdeleClass_mk`,
`continuousCharEquivSIdeleClass_mk`). The statements of the two isomorphisms use only kernels and
images and do not depend on the normalization; the value lemmas do.

**Intermediate objects** (for `Ω = AlgebraicClosure K`). For a continuous character `χ` of `G_S`:
`absoluteCharacter χ` is `χ` read on `Gal(AlgebraicClosure K / K)`; `characterField χ` is the
fixed field of its kernel, a finite abelian Galois extension of `K` contained in `K_S`
(`characterField_le`), hence unramified outside `S` (`isUnramifiedOutside_characterField`);
`ideleCharacter χ` is the continuous character `x ↦ χ(σ|_{K_S})` of the idèles; it kills the
narrow subgroup `K^× U^S_+` (`narrowSIdeleClassSubgroup_le_ker_ideleCharacter`) and so defines
`narrowSIdeleClassCharacter χ`. `narrowSIdeleClassCharacterHom K S n` is `χ ↦
narrowSIdeleClassCharacter χ`, a homomorphism, injective and, for finite `S`, surjective.

## Complete types

```lean
@Langlands.GaloisCohomology.absoluteCharacter : {K : Type u} →
  [inst : Field K] →
    [NumberField K] →
      {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} →
        {n : ℕ} →
          (Langlands.Galois.GaloisGroupUnramifiedOutside K (AlgebraicClosure K) S →ₜ* Multiplicative (ZMod n)) →
            Gal(AlgebraicClosure K/K) →ₜ* Multiplicative (ZMod n)

@Langlands.GaloisCohomology.absoluteCharacter_apply : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {n : ℕ}
  (χ : Langlands.Galois.GaloisGroupUnramifiedOutside K (AlgebraicClosure K) S →ₜ* Multiplicative (ZMod n))
  (σ : Gal(AlgebraicClosure K/K)),
  (Langlands.GaloisCohomology.absoluteCharacter χ) σ =
    χ ((Langlands.Galois.GaloisGroupUnramifiedOutside.quotientMap K (AlgebraicClosure K) S) σ)

@Langlands.GaloisCohomology.isOpen_ker_absoluteCharacter : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {n : ℕ}
  (χ : Langlands.Galois.GaloisGroupUnramifiedOutside K (AlgebraicClosure K) S →ₜ* Multiplicative (ZMod n)),
  IsOpen ↑(↑(Langlands.GaloisCohomology.absoluteCharacter χ)).ker

@Langlands.GaloisCohomology.isClosed_ker_absoluteCharacter : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {n : ℕ}
  (χ : Langlands.Galois.GaloisGroupUnramifiedOutside K (AlgebraicClosure K) S →ₜ* Multiplicative (ZMod n)),
  IsClosed ↑(↑(Langlands.GaloisCohomology.absoluteCharacter χ)).ker

@Langlands.GaloisCohomology.characterField : {K : Type u} →
  [inst : Field K] →
    [NumberField K] →
      {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} →
        {n : ℕ} →
          (Langlands.Galois.GaloisGroupUnramifiedOutside K (AlgebraicClosure K) S →ₜ* Multiplicative (ZMod n)) →
            IntermediateField K (AlgebraicClosure K)

@Langlands.GaloisCohomology.fixingSubgroup_characterField : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {n : ℕ}
  (χ : Langlands.Galois.GaloisGroupUnramifiedOutside K (AlgebraicClosure K) S →ₜ* Multiplicative (ZMod n)),
  (Langlands.GaloisCohomology.characterField χ).fixingSubgroup = (↑(Langlands.GaloisCohomology.absoluteCharacter χ)).ker

@Langlands.GaloisCohomology.finiteDimensional_characterField : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {n : ℕ}
  (χ : Langlands.Galois.GaloisGroupUnramifiedOutside K (AlgebraicClosure K) S →ₜ* Multiplicative (ZMod n)),
  FiniteDimensional K ↥(Langlands.GaloisCohomology.characterField χ)

@Langlands.GaloisCohomology.isGalois_characterField : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {n : ℕ}
  (χ : Langlands.Galois.GaloisGroupUnramifiedOutside K (AlgebraicClosure K) S →ₜ* Multiplicative (ZMod n)),
  IsGalois K ↥(Langlands.GaloisCohomology.characterField χ)

@Langlands.GaloisCohomology.absoluteCharacter_eq_one_iff : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {n : ℕ}
  (χ : Langlands.Galois.GaloisGroupUnramifiedOutside K (AlgebraicClosure K) S →ₜ* Multiplicative (ZMod n))
  (σ : Gal(AlgebraicClosure K/K)),
  (Langlands.GaloisCohomology.absoluteCharacter χ) σ = 1 ↔
    (AlgEquiv.restrictNormalHom ↥(Langlands.GaloisCohomology.characterField χ)) σ = 1

@Langlands.GaloisCohomology.isAbelianGalois_characterField : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {n : ℕ}
  (χ : Langlands.Galois.GaloisGroupUnramifiedOutside K (AlgebraicClosure K) S →ₜ* Multiplicative (ZMod n)),
  IsAbelianGalois K ↥(Langlands.GaloisCohomology.characterField χ)

@Langlands.GaloisCohomology.characterField_le : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {n : ℕ}
  (χ : Langlands.Galois.GaloisGroupUnramifiedOutside K (AlgebraicClosure K) S →ₜ* Multiplicative (ZMod n)),
  Langlands.GaloisCohomology.characterField χ ≤ Langlands.Galois.maximalUnramifiedOutside K (AlgebraicClosure K) S

@Langlands.GaloisCohomology.isUnramifiedOutside_characterField : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {n : ℕ}
  (χ : Langlands.Galois.GaloisGroupUnramifiedOutside K (AlgebraicClosure K) S →ₜ* Multiplicative (ZMod n)),
  Langlands.Galois.IsUnramifiedOutside S (Langlands.GaloisCohomology.characterField χ)

@Langlands.GaloisCohomology.ideleCharacter : {K : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} →
        {n : ℕ} →
          (Langlands.Galois.GaloisGroupUnramifiedOutside K (AlgebraicClosure K) S →ₜ* Multiplicative (ZMod n)) →
            Langlands.Global.Ideles K →ₜ* Multiplicative (ZMod n)

@Langlands.GaloisCohomology.ideleCharacter_apply : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {n : ℕ}
  (χ : Langlands.Galois.GaloisGroupUnramifiedOutside K (AlgebraicClosure K) S →ₜ* Multiplicative (ZMod n))
  (x : Langlands.Global.Ideles K) (σ : Gal(AlgebraicClosure K/K)),
  (Langlands.LocalClassField.absoluteAbelianizationProjection K) σ =
      (Langlands.ClassFieldTheory.Global.Artin.geometricArtinMap K) ((Langlands.Global.ideleClassMap K) x) →
    (Langlands.GaloisCohomology.ideleCharacter χ) x =
      χ ((Langlands.Galois.GaloisGroupUnramifiedOutside.quotientMap K (AlgebraicClosure K) S) σ)

@Langlands.GaloisCohomology.exists_absoluteAbelianizationProjection_eq : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K] (x : Langlands.Global.IdeleClasses K),
  ∃ σ,
    (Langlands.LocalClassField.absoluteAbelianizationProjection K) σ =
      (Langlands.ClassFieldTheory.Global.Artin.geometricArtinMap K) x

@Langlands.GaloisCohomology.ideleCharacter_finiteIdeleInclusion : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {n : ℕ}
  (χ : Langlands.Galois.GaloisGroupUnramifiedOutside K (AlgebraicClosure K) S →ₜ* Multiplicative (ZMod n))
  {v : Langlands.Global.FinitePlace K},
  v ∉ S →
    ∀ {a : (Langlands.Global.FiniteCompletion K v)ˣ},
      a ∈ (Submonoid.ofClass (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v)).units →
        (Langlands.GaloisCohomology.ideleCharacter χ) ((Langlands.Global.finiteIdeleInclusion K v) a) = 1

@Langlands.GaloisCohomology.narrowSIdeleClassSubgroup_le_ker_ideleCharacter : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {n : ℕ}
  (χ : Langlands.Galois.GaloisGroupUnramifiedOutside K (AlgebraicClosure K) S →ₜ* Multiplicative (ZMod n)) [NeZero n],
  Langlands.GaloisCohomology.narrowSIdeleClassSubgroup S ≤ (↑(Langlands.GaloisCohomology.ideleCharacter χ)).ker

@Langlands.GaloisCohomology.narrowSIdeleClassCharacter : {K : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} →
        {n : ℕ} →
          (Langlands.Galois.GaloisGroupUnramifiedOutside K (AlgebraicClosure K) S →ₜ* Multiplicative (ZMod n)) →
            [NeZero n] → Langlands.GaloisCohomology.NarrowSIdeleClassGroup S →* Multiplicative (ZMod n)

@Langlands.GaloisCohomology.narrowSIdeleClassCharacter_mk : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {n : ℕ}
  (χ : Langlands.Galois.GaloisGroupUnramifiedOutside K (AlgebraicClosure K) S →ₜ* Multiplicative (ZMod n))
  [inst_2 : NeZero n] (x : Langlands.Global.Ideles K) (σ : Gal(AlgebraicClosure K/K)),
  (Langlands.LocalClassField.absoluteAbelianizationProjection K) σ =
      (Langlands.ClassFieldTheory.Global.Artin.geometricArtinMap K) ((Langlands.Global.ideleClassMap K) x) →
    (Langlands.GaloisCohomology.narrowSIdeleClassCharacter χ)
        ((Langlands.GaloisCohomology.NarrowSIdeleClassGroup.mk S) x) =
      χ ((Langlands.Galois.GaloisGroupUnramifiedOutside.quotientMap K (AlgebraicClosure K) S) σ)

@Langlands.GaloisCohomology.narrowSIdeleClassCharacterHom : (K : Type u) →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
        (n : ℕ) →
          [NeZero n] →
            (Langlands.Galois.GaloisGroupUnramifiedOutside K (AlgebraicClosure K) S →ₜ* Multiplicative (ZMod n)) →*
              Langlands.GaloisCohomology.NarrowSIdeleClassGroup S →* Multiplicative (ZMod n)

@Langlands.GaloisCohomology.narrowSIdeleClassCharacterHom_apply : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {n : ℕ}
  (χ : Langlands.Galois.GaloisGroupUnramifiedOutside K (AlgebraicClosure K) S →ₜ* Multiplicative (ZMod n))
  [inst_2 : NeZero n],
  (Langlands.GaloisCohomology.narrowSIdeleClassCharacterHom K S n) χ =
    Langlands.GaloisCohomology.narrowSIdeleClassCharacter χ

@Langlands.GaloisCohomology.narrowSIdeleClassCharacterHom_injective : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {n : ℕ} [inst_2 : NeZero n],
  Function.Injective ⇑(Langlands.GaloisCohomology.narrowSIdeleClassCharacterHom K S n)

@Langlands.GaloisCohomology.narrowSIdeleClassCharacterHom_surjective : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {n : ℕ} [inst_2 : NeZero n],
  S.Finite → Function.Surjective ⇑(Langlands.GaloisCohomology.narrowSIdeleClassCharacterHom K S n)

@Langlands.GaloisCohomology.continuousCharCongr : {G : Type u_1} →
  {H : Type u_2} →
    [inst : Group G] →
      [inst_1 : TopologicalSpace G] →
        [inst_2 : Group H] →
          [inst_3 : TopologicalSpace H] →
            G ≃ₜ* H → (n : ℕ) → (H →ₜ* Multiplicative (ZMod n)) ≃* (G →ₜ* Multiplicative (ZMod n))

@Langlands.GaloisCohomology.continuousCharCongr_apply : ∀ {G : Type u_1} {H : Type u_2} [inst : Group G] [inst_1 : TopologicalSpace G] [inst_2 : Group H]
  [inst_3 : TopologicalSpace H] (f : G ≃ₜ* H) (n : ℕ) (χ : H →ₜ* Multiplicative (ZMod n)) (x : G),
  ((Langlands.GaloisCohomology.continuousCharCongr f n) χ) x = χ (f x)

@Langlands.GaloisCohomology.continuousCharEquivNarrowSIdeleClass : {K : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      (Ω : Type v) →
        [inst_2 : Field Ω] →
          [inst_3 : Algebra K Ω] →
            [IsSepClosure K Ω] →
              {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} →
                S.Finite →
                  (n : ℕ) →
                    [NeZero n] →
                      (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S →ₜ* Multiplicative (ZMod n)) ≃*
                        (Langlands.GaloisCohomology.NarrowSIdeleClassGroup S →* Multiplicative (ZMod n))

@Langlands.GaloisCohomology.absoluteAbelianizationProjection_autCongr_eq : ∀ {K : Type u} [inst : Field K] {Ω : Type v} [inst_1 : Field Ω] [inst_2 : Algebra K Ω]
  (e e' : Ω ≃ₐ[K] AlgebraicClosure K) (σ : Gal(Ω/K)),
  (Langlands.LocalClassField.absoluteAbelianizationProjection K) (e.autCongr σ) =
    (Langlands.LocalClassField.absoluteAbelianizationProjection K) (e'.autCongr σ)

@Langlands.GaloisCohomology.continuousCharEquivNarrowSIdeleClass_mk : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K] (Ω : Type v) [inst_2 : Field Ω] [inst_3 : Algebra K Ω]
  [inst_4 : IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hS : S.Finite) (n : ℕ) [inst_5 : NeZero n]
  (χ : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S →ₜ* Multiplicative (ZMod n)) (x : Langlands.Global.Ideles K)
  (e : Ω ≃ₐ[K] AlgebraicClosure K) (σ : Gal(Ω/K)),
  (Langlands.LocalClassField.absoluteAbelianizationProjection K) (e.autCongr σ) =
      (Langlands.ClassFieldTheory.Global.Artin.geometricArtinMap K) ((Langlands.Global.ideleClassMap K) x) →
    ((Langlands.GaloisCohomology.continuousCharEquivNarrowSIdeleClass Ω hS n) χ)
        ((Langlands.GaloisCohomology.NarrowSIdeleClassGroup.mk S) x) =
      χ ((Langlands.Galois.GaloisGroupUnramifiedOutside.quotientMap K Ω S) σ)

@Langlands.GaloisCohomology.continuousCharEquivSIdeleClass : {K : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      (Ω : Type v) →
        [inst_2 : Field Ω] →
          [inst_3 : Algebra K Ω] →
            [IsSepClosure K Ω] →
              {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} →
                S.Finite →
                  {n : ℕ} →
                    [NeZero n] →
                      Odd n ∨ NumberField.IsTotallyComplex K →
                        (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S →ₜ* Multiplicative (ZMod n)) ≃*
                          (Langlands.GaloisCohomology.SIdeleClassGroup S →* Multiplicative (ZMod n))

@Langlands.GaloisCohomology.precompToSIdeleClassGroup_continuousCharEquivSIdeleClass : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K] (Ω : Type v) [inst_2 : Field Ω] [inst_3 : Algebra K Ω]
  [inst_4 : IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hS : S.Finite) {n : ℕ} [inst_5 : NeZero n] (h : Odd n ∨ NumberField.IsTotallyComplex K)
  (χ : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S →ₜ* Multiplicative (ZMod n)),
  (Langlands.GaloisCohomology.NarrowSIdeleClassGroup.precompToSIdeleClassGroup S n)
      ((Langlands.GaloisCohomology.continuousCharEquivSIdeleClass Ω hS h) χ) =
    (Langlands.GaloisCohomology.continuousCharEquivNarrowSIdeleClass Ω hS n) χ

@Langlands.GaloisCohomology.continuousCharEquivSIdeleClass_mk : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K] (Ω : Type v) [inst_2 : Field Ω] [inst_3 : Algebra K Ω]
  [inst_4 : IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hS : S.Finite) {n : ℕ} [inst_5 : NeZero n] (h : Odd n ∨ NumberField.IsTotallyComplex K)
  (χ : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S →ₜ* Multiplicative (ZMod n)) (x : Langlands.Global.Ideles K)
  (e : Ω ≃ₐ[K] AlgebraicClosure K) (σ : Gal(Ω/K)),
  (Langlands.LocalClassField.absoluteAbelianizationProjection K) (e.autCongr σ) =
      (Langlands.ClassFieldTheory.Global.Artin.geometricArtinMap K) ((Langlands.Global.ideleClassMap K) x) →
    ((Langlands.GaloisCohomology.continuousCharEquivSIdeleClass Ω hS h) χ)
        ((Langlands.GaloisCohomology.SIdeleClassGroup.mk S) x) =
      χ ((Langlands.Galois.GaloisGroupUnramifiedOutside.quotientMap K Ω S) σ)
```

## Outline of the proofs

1. *The character of the idèles kills `U^S_+`.* `absoluteCharacter χ` factors through the
   topological abelianization (`LocalClassField.abelianizationLift`), so `ideleCharacter χ` is a
   continuous character of the idèles with values in `ℤ/n`. At a finite place `v ∉ S` and an
   integral unit `a` of `K_v`, let `σ` lift the Artin symbol of `a`; its restriction to the field
   `E` of `χ` is `(arithmeticFiniteArtin K E a)⁻¹` (`restrictNormalHom_eq_inv_arithmeticFiniteArtin`),
   and `arithmeticFiniteArtin K E a = 1` because every prime of `E` above `v` is unramified
   (`arithmeticFiniteArtin_finiteClassInclusion_units_eq_one_iff`); so `σ` fixes `E` and
   `χ(σ) = 1` (`ideleCharacter_finiteIdeleInclusion`). By `positiveUnitIdelesOutside_le_ker` the
   character kills `U^S_+`.
2. *Injectivity.* Every element of `G_S` is the restriction of some `σ`, and the image of `σ` in
   the abelianization is an Artin symbol (`geometricArtinMap_surjective`).
3. *Surjectivity* (`S` finite). A homomorphism `ψ` from the narrow group to `ℤ/n` kills the `n`-th
   powers, so the preimage of its kernel in the idèles is open
   (`isOpen_of_pow_mem_of_positiveUnitIdelesOutside_le`), and so is its kernel `H` in the idèle
   class group. Let `E = classField K H` (the existence theorem of the module
   `Langlands.ClassFieldTheory.Global.Artin.ClassField`): `ker (arithmeticFiniteArtin K E) = H`.
   The integral local units at `v ∉ S` lie in `U^S_+`, hence in `H`, so every prime of `E` above
   `v` is unramified, `E ⊆ K_S` (`isUnramifiedOutside_iff_le`). Write `ψ = θ ∘ arithmeticFiniteArtin
   K E` on idèle classes; then `σ ↦ θ(σ|_E)⁻¹` is a continuous character of `Gal(AlgebraicClosure K
   / K)` trivial on `Gal(AlgebraicClosure K / K_S)`, so it descends to `G_S`, and its image is `ψ`
   by `restrictNormalHom_eq_inv_arithmeticFiniteArtin`.
4. *Any separable closure.* `continuousCharCongr` and `galoisGroupUnramifiedOutsideCongr` (of the
   module `Langlands.Galois.RestrictedRamification.ClosureChange`) transport characters
   along `IsSepClosure.equiv K (AlgebraicClosure K) Ω`. The value lemma holds for every isomorphism
   `e`: two conjugates of `σ` differ by an inner automorphism, which does not change the image in
   the abelianization (`absoluteAbelianizationProjection_autCongr_eq`).

Theorems of the Library's Artin files used: `geometricArtinMap`, `geometricArtinMap_surjective`,
`restrictNormalHom_eq_inv_arithmeticFiniteArtin` (`ArtinMap`); `arithmeticFiniteArtin`,
`arithmeticFiniteArtin_surjective` (`FiniteArtin`); `classField`, `arithmeticFiniteArtin_classField_ker`
(`ClassField`); `arithmeticFiniteArtin_finiteClassInclusion_units_eq_one_iff`
(`FiniteArtinUnramified`). No theorem of the NYLL copy is named in this file; the copy is used
through these files.

## Declarations

In the order of the file:

- `absoluteCharacter` (def): A continuous character of `G_S`, read on the absolute Galois group.
- `absoluteCharacter_apply` (theorem): The value of `absoluteCharacter χ`.
- `isOpen_ker_absoluteCharacter` (theorem): The kernel of `absoluteCharacter χ` is open.
- `isClosed_ker_absoluteCharacter` (theorem): The kernel of `absoluteCharacter χ` is closed.
- `characterField` (def): The finite abelian extension of `K` cut out by a continuous character `χ` of `G_S`: the fixed field in `AlgebraicClosure K` of the kernel of `χ` read on the absolute Galois group.
- `fixingSubgroup_characterField` (theorem): The fixing subgroup of the field of `χ` is the kernel of `absoluteCharacter χ`.
- `finiteDimensional_characterField` (instance): The field of `χ` is finite over `K`.
- `isGalois_characterField` (instance): The field of `χ` is Galois over `K`.
- `absoluteCharacter_eq_one_iff` (theorem): `χ σ` depends only on the restriction of `σ` to the field of `χ`.
- `isAbelianGalois_characterField` (instance): The field of `χ` is abelian over `K`.
- `characterField_le` (theorem): The field of a character of `G_S` lies in the maximal extension unramified outside `S`.
- `isUnramifiedOutside_characterField` (theorem): The field of a character of `G_S` is unramified outside `S`.
- `ideleCharacter` (def): The character of the idèles attached to a continuous character `χ` of `G_S`: `χ` of the restriction to `K_S` of any element of the absolute Galois group whose image in the abelianization is the image of the idèle under the global Artin map `geometricArtinMap K` (`ideleCharacter_apply`).
- `ideleCharacter_apply` (theorem): The value of `ideleCharacter χ` at an idèle `x`: `χ` of the restriction to `K_S` of any `σ` lifting `geometricArtinMap K x`.
- `exists_absoluteAbelianizationProjection_eq` (theorem): Every value of the Artin map lifts to the absolute Galois group.
- `ideleCharacter_finiteIdeleInclusion` (theorem): The idèle character of a character of `G_S` kills the integral local units at every finite place outside `S`: the field of the character is unramified there.
- `narrowSIdeleClassSubgroup_le_ker_ideleCharacter` (theorem): `ideleCharacter χ` kills `K^× U^S_+`.
- `narrowSIdeleClassCharacter` (def): The character of the narrow `S`-idèle class group attached to a continuous character `χ` of `G_S` (for `Ω = AlgebraicClosure K`).
- `narrowSIdeleClassCharacter_mk` (theorem): The value of `narrowSIdeleClassCharacter χ` on the class of an idèle `x`.
- `narrowSIdeleClassCharacterHom` (def): `χ ↦ narrowSIdeleClassCharacter χ`, as a homomorphism of groups.
- `narrowSIdeleClassCharacterHom_apply` (theorem): The value of `narrowSIdeleClassCharacterHom`.
- `narrowSIdeleClassCharacterHom_injective` (theorem): `narrowSIdeleClassCharacterHom` is injective: the Artin map is surjective.
- `narrowSIdeleClassCharacterHom_surjective` (theorem): For finite `S`, every homomorphism from the narrow `S`-idèle class group to `ℤ/n` comes from a continuous character of `G_S`. Its kernel in the idèle class group is open (it contains the `n`-th powers and the image of `positiveUnitIdelesOutside S`), so it is the kernel of the Artin map of its class field `E` (`classField`); `E` is unramified outside `S` because the integral local units outside `S` lie in that kernel, hence `E ⊆ K_S`; the character is `σ ↦ θ(σ|_E)⁻¹`, where `θ ∘ arithmeticFiniteArtin K E` is the given homomorphism on idèle classes.
- `continuousCharCongr` (def): Precomposition with an isomorphism of topological groups, on continuous characters with values in `ℤ/n`.
- `continuousCharCongr_apply` (theorem): The value of `continuousCharCongr f n χ`.
- `continuousCharEquivNarrowSIdeleClass` (def): **Characters of `G_S` by narrow `S`-idèle classes.** For a number field `K`, a separable closure `Ω` of `K`, a finite set `S` of finite places of `K` and `n ≠ 0`, the continuous characters of `G_S = Gal(K_S / K)` with values in `ℤ/n` correspond to the homomorphisms from the narrow `S`-idèle class group `I_K / K^× U^S_+` to `ℤ/n`: a character `χ` goes to `x ↦ χ(σ|_{K_S})` for `σ` with image `geometricArtinMap K x` in the abelianized absolute Galois group (`continuousCharEquivNarrowSIdeleClass_mk`). No condition on `n` or on the real places.
- `absoluteAbelianizationProjection_autCongr_eq` (theorem): Conjugation by an isomorphism of algebraic closures does not change the image of an element of the absolute Galois group in the abelianization.
- `continuousCharEquivNarrowSIdeleClass_mk` (theorem): The value of `continuousCharEquivNarrowSIdeleClass` on the class of an idèle `x`: `χ` of the restriction to `K_S` of any `σ ∈ Gal(Ω / K)` whose conjugate into `AlgebraicClosure K`, by any isomorphism `e`, maps to `geometricArtinMap K x` in the abelianization.
- `continuousCharEquivSIdeleClass` (def): **Characters of `G_S` by `S`-idèle classes.** For a number field `K`, a separable closure `Ω` of `K`, a finite set `S` of finite places of `K` and `n ≠ 0` with `n` odd or `K` totally complex, the continuous characters of `G_S = Gal(K_S / K)` with values in `ℤ/n` correspond to the homomorphisms from the `S`-idèle class group `I_K / K^× U^S` to `ℤ/n` (`continuousCharEquivSIdeleClass_mk`).
- `precompToSIdeleClassGroup_continuousCharEquivSIdeleClass` (theorem): Read on the narrow group, `continuousCharEquivSIdeleClass` is `continuousCharEquivNarrowSIdeleClass`.
- `continuousCharEquivSIdeleClass_mk` (theorem): The value of `continuousCharEquivSIdeleClass` on the class of an idèle `x`: `χ` of the restriction to `K_S` of any `σ ∈ Gal(Ω / K)` whose conjugate into `AlgebraicClosure K` maps to `geometricArtinMap K x` in the abelianization.

## Source and licence

The structure of the construction follows the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files
`src/GroundTheory/ProfiniteCohomology/RestrictedRamification/ClassFieldGS.lean` (`charAbs`,
`isOpen_ker_charAbs`, `isClosed_ker_charAbs`, `charField`, `fixingSubgroup_charField`, the instances
on `charField`, `charAbs_eq_one_iff`, `charField_le`, `isUnramifiedOutside_charField`,
`charToSIdelePos`, `charToSIdelePosHom`, `charToSIdelePosHom_injective`,
`charToSIdelePosHom_surjective`, `charEquivPos`) and `ClassFieldGSFull.lean` (`charEquiv`,
`precompPos_charEquiv`, `charEquiv_mk_eq`). The repository has no licence file; its text is used
with attribution (`licenses/RiemannHypothesis/SOURCE.md`).
Changes: the proofs rest on the Library's global Artin map and existence theorem in place of the
source's class field theory (`artinMap`, `reciprocityMap`, `ker_reciprocityMap`,
`exists_intermediateField_range_ideleClassNorm_eq_of_finiteIndex`, conductors); the source's
openness and unramifiedness arguments through moduli are replaced by
`isOpen_of_pow_mem_of_positiveUnitIdelesOutside_le` and the unit criterion; the field is any
separable closure `Ω` in another universe than `K` (the source: `IsAlgClosure K Ω`, one universe);
the names are new (`absoluteCharacter`, `characterField`, `narrowSIdeleClassCharacter`,
`continuousCharEquivNarrowSIdeleClass`, `continuousCharEquivSIdeleClass`).

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition, corrected
  printing (Springer, 2013), Chapter VIII, §3: p. 454 (the `S`-idèle class group); Theorem
  (8.3.13), p. 459 (for `S ⊇ S_∞`, the exact sequence `0 → D_S(k) → C_S(k) → G_S^ab → 0` with
  `D_S(k)` the connected component, divisible); p. 460, proof of (8.3.13) and Corollary (8.3.14)
  (the units at `p ∉ S` go to inertia; the open subgroups of `C_S(k)` are the norm groups of
  finite Galois extensions inside `k_S`). The narrow group of this file is `C_{S ∪ S_∞}(k)` modulo
  the identity component of the archimedean idèles; its homomorphisms to `ℤ/n` are continuous for
  finite `S` and kill the divisible group `D_S(k)`, which is how the isomorphism above follows
  from (8.3.13); the proof here does not pass through (8.3.13).
- J. Neukirch, *Algebraic Number Theory* (Springer, 1999), Chapter VI: Theorem (5.5) and
  Proposition (5.6), p. 391 (the global norm residue symbol and its compatibility with the local
  ones); Theorem (6.1), p. 395 (existence theorem: finite abelian extensions and closed subgroups
  of finite index of `C_K`); Chapter V, Definition (1.6) and Proposition (1.7), p. 323 (a finite
  abelian extension of a local field is unramified exactly when the units are norms). Both
  normalize arithmetically; `geometricArtinMap` is the inverse of their maps.
