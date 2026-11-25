# Artin lifts of uniformizers and geometric Frobenius lifts

`Langlands/GaloisCohomology/Global/Abelianization/ArtinFrobenius.lean`, namespace `Langlands.GaloisCohomology`.

For a number field `K`, a finite place `v` and the completion `K_v`, this file compares the
arithmetic Artin lifts of local class field theory (`IsArithmeticArtinLift`, for the local-field
structure `FiniteCompletion.valuativeRel v` of `K_v`) with the geometric Frobenius lifts
`IsGeometricFrobeniusLift v` of `Langlands.GaloisRepresentation` (defined through the residue action
on the spectral integers of `AlgebraicClosure K_v` for the norm of `K_v`, the instance of
`open scoped Valued`), and evaluates the characters of the `S`-idèle class group attached to
characters of `G_S` at the places outside `S` by local class field theory.

**Main statements.**
* `residueHom_eq_pow_of_isArithmeticArtinLift`: for a nonarchimedean local field `F`, an arithmetic
  Artin lift `σ ∈ Gal(AlgebraicClosure F / F)` of an element of normalized order `1` acts on the
  residue field of the spectral integers of `AlgebraicClosure F` as `x ↦ x ^ q`, `q` the order of
  the residue field of `F`.
* It uses `extensionIntegers_eq_localClosureIntegers` (the spectral integers of `AlgebraicClosure K_v`
  for the norm of `K_v` and for its local-field structure coincide) and
  `card_residueField_localNormedField` (the residue field of `K_v` for its local-field structure has
  `N(v)` elements) of the module `Langlands.Galois.FrobeniusLift`.
* `isGeometricFrobeniusLift_inv_of_isArithmeticArtinLift`: the inverse of an arithmetic Artin lift
  of an element of `K_v` of normalized order `1` is a geometric Frobenius lift at `v`;
  `normalizedUnitOrder_localUniformizer_eq_one`: `localUniformizer v` has normalized order `1`.
* `apply_quotientMap_autCongr_localToGlobalGalois`: a homomorphism from `G_S` to a commutative group
  takes the same value at `localizationHom ι S v σ` and at `σ` mapped by `localToGlobalGalois v` and
  carried to `Gal(Ω / K)` by an isomorphism `AlgebraicClosure K ≃ₐ[K] Ω`.
* `continuousCharEquivSIdeleClass_sPresentation_one_single_of_isArithmeticArtinLift`: for a
  continuous character `χ` of `G_S` with values in `ℤ/n` and `v ∉ S`,
  `continuousCharEquivSIdeleClass χ` takes at the generator of the divisors prime to `S` at `v` the
  value `χ(σ)⁻¹`, `σ` an arithmetic Artin lift of `localUniformizer v` read in `G_S` through
  `localizationHom ι S v`.

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.towerSpectralIntegerMap.{u_1, u_2, u_3} (K : Type u_1) (L : Type u_2) (E : Type u_3)
  [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  [Field E] [Algebra K E] [Algebra E L] [IsScalarTower K E L] [Algebra.IsAlgebraic K E] :
  ↥(Langlands.LocalGalois.extensionIntegers K E) →+* ↥(Langlands.LocalGalois.extensionIntegers K L)
Langlands.GaloisCohomology.towerSpectralIntegerMap_isLocalHom.{u_1, u_2, u_3} (K : Type u_1) (L : Type u_2)
  (E : Type u_3) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] [Field E] [Algebra K E] [Algebra E L] [IsScalarTower K E L] [Algebra.IsAlgebraic K E] :
  IsLocalHom (Langlands.GaloisCohomology.towerSpectralIntegerMap K L E)
Langlands.GaloisCohomology.towerSpectralResidueMap.{u_1, u_2, u_3} (K : Type u_1) (L : Type u_2) (E : Type u_3)
  [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  [Field E] [Algebra K E] [Algebra E L] [IsScalarTower K E L] [Algebra.IsAlgebraic K E] :
  IsLocalRing.ResidueField ↥(Langlands.LocalGalois.extensionIntegers K E) →+*
    IsLocalRing.ResidueField ↥(Langlands.LocalGalois.extensionIntegers K L)
Langlands.GaloisCohomology.towerSpectralResidueMap_residue.{u_1, u_2, u_3} (K : Type u_1) (L : Type u_2) (E : Type u_3)
  [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  [Field E] [Algebra K E] [Algebra E L] [IsScalarTower K E L] [Algebra.IsAlgebraic K E]
  (x : ↥(Langlands.LocalGalois.extensionIntegers K E)) :
  (Langlands.GaloisCohomology.towerSpectralResidueMap K L E)
      ((IsLocalRing.residue ↥(Langlands.LocalGalois.extensionIntegers K E)) x) =
    (IsLocalRing.residue ↥(Langlands.LocalGalois.extensionIntegers K L))
      ((Langlands.GaloisCohomology.towerSpectralIntegerMap K L E) x)
Langlands.GaloisCohomology.towerSpectralResidueMap_residueHom.{u_1, u_2, u_3} (K : Type u_1) (L : Type u_2)
  (E : Type u_3) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] [Field E] [Algebra K E] [Algebra E L] [IsScalarTower K E L] [Normal K E] (σ : Gal(L/K))
  (y : IsLocalRing.ResidueField ↥(Langlands.LocalGalois.extensionIntegers K E)) :
  (Langlands.GaloisCohomology.towerSpectralResidueMap K L E)
      (((Langlands.LocalGalois.residueHom K E) ((AlgEquiv.restrictNormalHom E) σ)) y) =
    ((Langlands.LocalGalois.residueHom K L) σ) ((Langlands.GaloisCohomology.towerSpectralResidueMap K L E) y)
Langlands.GaloisCohomology.residueHom_eq_pow_iff.{u_1, u_2} (K : Type u_1) (L : Type u_2) [NontriviallyNormedField K]
  [IsUltrametricDist K] [CompleteSpace K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] (σ : Gal(L/K)) (q : ℕ) :
  (∀ (x : IsLocalRing.ResidueField ↥(Langlands.LocalGalois.extensionIntegers K L)),
      ((Langlands.LocalGalois.residueHom K L) σ) x = x ^ q) ↔
    ∀ y ∈ Langlands.LocalGalois.extensionIntegers K L,
      (Langlands.LocalGalois.extensionIntegers K L).valuation (σ y - y ^ q) < 1
Langlands.GaloisCohomology.mem_range_of_pow_card_eq.{u_1, u_2} {k : Type u_1} {k' : Type u_2} [Field k] [Fintype k]
  [Field k'] (j : k →+* k') {x : k'} (hx : x ^ Fintype.card k = x) : x ∈ Set.range ⇑j
Langlands.GaloisCohomology.residueHom_eq_pow_of_isArithmeticArtinLift.{u} (F : Type u) [Field F] [ValuativeRel F]
  [TopologicalSpace F] [IsNonarchimedeanLocalField F] {π : Fˣ}
  (hπ : (Langlands.ClassFieldTheory.Local.normalizedUnitOrder F) (Additive.ofMul π) = 1) {σ : Gal(AlgebraicClosure F/F)}
  (hσ : Langlands.ClassFieldTheory.Local.Artin.IsArithmeticArtinLift F (AlgebraicClosure F) π σ)
  (x : IsLocalRing.ResidueField ↥(Langlands.LocalGalois.extensionIntegers F (AlgebraicClosure F))) :
  ((Langlands.LocalGalois.residueHom F (AlgebraicClosure F)) σ) x =
    x ^ Nat.card (IsLocalRing.ResidueField ↥(Langlands.LocalGalois.baseIntegers F))
Langlands.GaloisCohomology.isGeometricFrobeniusLift_inv_of_isArithmeticArtinLift.{u} {K : Type u} [Field K]
  [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  {π : (Langlands.Global.FiniteCompletion K v)ˣ}
  (hπ :
    (Langlands.ClassFieldTheory.Local.normalizedUnitOrder (Langlands.Global.FiniteCompletion K v)) (Additive.ofMul π) =
      1)
  {σ : Langlands.GaloisRepresentation.LocalGroup v}
  (hσ :
    Langlands.ClassFieldTheory.Local.Artin.IsArithmeticArtinLift (Langlands.Global.FiniteCompletion K v)
      (AlgebraicClosure (Langlands.Global.FiniteCompletion K v)) π σ) :
  Langlands.GaloisRepresentation.IsGeometricFrobeniusLift v σ⁻¹
Langlands.GaloisCohomology.normalizedUnitOrder_localUniformizer_eq_one.{u} {K : Type u} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
  (Langlands.ClassFieldTheory.Local.normalizedUnitOrder (Langlands.Global.FiniteCompletion K v))
      (Additive.ofMul (Langlands.GaloisCohomology.localUniformizer v)) =
    1
Langlands.GaloisCohomology.localToGlobalGalois_eq_decompositionHom.{u} {K : Type u} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (σ :
    Gal(AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion K
          v)/IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) :
  (Langlands.GaloisRepresentation.localToGlobalGalois v) σ =
    (Langlands.Galois.decompositionHom (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
        ((Langlands.Galois.PlaceEmbeddings.standard K).finite v))
      σ
Langlands.GaloisCohomology.autCongr_decompositionHom.{u, u_1, u_2, u_3} {K : Type u} [Field K] {Ω : Type u} [Field Ω]
  [Algebra K Ω] {A : Type u_1} {Kv : Type u_2} {Ωv : Type u_3} [Field A] [Algebra K A] [Field Kv] [Field Ωv]
  [Algebra K Kv] [Algebra Kv Ωv] [Algebra K Ωv] [IsScalarTower K Kv Ωv] [Normal K A] [Normal K Ω] (f : A ≃ₐ[K] Ω)
  (j : A →ₐ[K] Ωv) (σ : Gal(Ωv/Kv)) :
  f.autCongr ((Langlands.Galois.decompositionHom Kv j) σ) = (Langlands.Galois.decompositionHom Kv (j.comp ↑f.symm)) σ
Langlands.GaloisCohomology.apply_quotientMap_autCongr_localToGlobalGalois.{u, u_1} {K : Type u} [Field K]
  [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {M : Type u_1} [CommGroup M]
  (χ : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S →* M) (f : AlgebraicClosure K ≃ₐ[K] Ω)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (σ :
    Gal(AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion K
          v)/IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) :
  χ
      ((Langlands.Galois.GaloisGroupUnramifiedOutside.quotientMap K Ω S)
        (f.autCongr ((Langlands.GaloisRepresentation.localToGlobalGalois v) σ))) =
    χ ((Langlands.Galois.localizationHom ι S v) σ)
Langlands.GaloisCohomology.continuousCharEquivSIdeleClass_sPresentation_one_single_of_isArithmeticArtinLift.{u}
  {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {n : ℕ} [NeZero n] [Finite ↑S]
  (h : Odd n ∨ NumberField.IsTotallyComplex K)
  (χ : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S →ₜ* Multiplicative (ZMod n))
  {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)} (hv : v ∉ S)
  (σ :
    Gal(AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)/IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
  (hσ :
    Langlands.ClassFieldTheory.Local.Artin.IsArithmeticArtinLift (Langlands.Global.FiniteCompletion K v)
      (AlgebraicClosure (Langlands.Global.FiniteCompletion K v)) (Langlands.GaloisCohomology.localUniformizer v) σ) :
  ((Langlands.GaloisCohomology.continuousCharEquivSIdeleClass Ω ⋯ h) χ)
      ((Langlands.GaloisCohomology.sPresentation S) (1, Multiplicative.ofAdd fun₀ | ⟨v, hv⟩ => 1)) =
    (χ ((Langlands.Galois.localizationHom ι S v) σ))⁻¹
```

## Outline of the proofs

A residue element `x` of `AlgebraicClosure F` generates a finite extension of degree `m` of the
residue field `k` of `F`, so `x ^ (q ^ m) = x`; the unramified extension `E` of degree `m`
(`exists_finiteUnramified_finrank`), embedded in `AlgebraicClosure F`, has a residue field with
`q ^ m` elements, whose image contains all roots of `X ^ (q ^ m) - X` (`mem_range_of_pow_card_eq`),
among them `x`. On `E`, `σ` restricts to the arithmetic Artin symbol of `π`
(`IsArithmeticArtinLift.restrictNormalHom_eq`), which acts on residues as `y ↦ y ^ q`
(`residueHom_arithmeticFiniteArtin`), and restriction is compatible with the residue actions
(`towerSpectralResidueMap_residueHom`).

The two normed structures on `K_v` (`Valued.toNontriviallyNormedField` and `localNormedField`) have
the same valuation ring, the elements of valuation at most `1` (`normedField_valuation_integer_eq` of
`Langlands.Galois.FrobeniusLift`),
so the spectral integers of `AlgebraicClosure K_v`, the integral closures of that ring
(`integral_iff_mem_spectralIntegers`, `closureIntegers_integral`), coincide; the statement on the
residue actions is read on the valuation subring (`residueHom_eq_pow_iff`). The normalized order of
`localUniformizer v` is `1`: the valuation of `K_v` and the normalized valuation of its local-field
structure have the same elements of valuation `1`, and comparing with an element of normalized order
`1` gives `m k = 1` for the two orders.

`localToGlobalGalois v` is the decomposition homomorphism of the standard embedding of
`AlgebraicClosure K` into `AlgebraicClosure K_v` (`PlaceEmbeddings.decompositionHom_standard_finite`);
carried to `Ω` it is the decomposition homomorphism of an embedding of `Ω` which differs from
`ι.finite v` by an automorphism of `Ω` (`exists_eq_comp_of_normal`), hence a conjugate of it
(`decompositionHom_comp`). With `continuousCharEquivSIdeleClass_sPresentation_one_single` for the
geometric Frobenius lift `σ⁻¹` this gives the value `χ(σ⁻¹) = χ(σ)⁻¹`.

## Declarations

In the order of the file:

- `towerSpectralIntegerMap` (def): The map of spectral integers along a tower `K ⊆ E ⊆ L` of algebraic extensions.
- `towerSpectralIntegerMap_isLocalHom` (instance).
- `towerSpectralResidueMap` (def): The map of residue fields along a tower `K ⊆ E ⊆ L`.
- `towerSpectralResidueMap_residue` (theorem).
- `towerSpectralResidueMap_residueHom` (theorem): Restriction to a normal intermediate extension is compatible with the residue actions.
- `residueHom_eq_pow_iff` (theorem): The residue action of `σ` is `x ↦ x ^ q` exactly when `σ y - y ^ q` lies in the maximal ideal for all spectral integers `y`.
- `mem_range_of_pow_card_eq` (theorem): An element `x` with `x ^ q = x`, `q` the order of a finite field `k`, lies in the image of any ring homomorphism from `k`.
- `residueHom_eq_pow_of_isArithmeticArtinLift` (theorem): **The residue action of an Artin lift of an element of order one.** An arithmetic Artin lift `σ` of an element of normalized order `1` acts on the residue field of the spectral integers of `AlgebraicClosure F` as `x ↦ x ^ q`, `q` the order of the residue field of `F`.
- `isGeometricFrobeniusLift_inv_of_isArithmeticArtinLift` (theorem): **An Artin lift of an element of order one is the inverse of a geometric Frobenius lift.** For an element `π` of `K_v` of normalized order `1` and an arithmetic Artin lift `σ` of `π` (local class field theory), `σ⁻¹` is a geometric Frobenius lift at `v`: `σ` acts on the residue field of `AlgebraicClosure K_v` as `x ↦ x ^ N(v)`.
- `normalizedUnitOrder_localUniformizer_eq_one` (theorem): The image of `globalUniformizer v` in `K_v` has normalized order `1`.
- `localToGlobalGalois_eq_decompositionHom` (theorem): `localToGlobalGalois v` is the decomposition homomorphism of the standard embedding of `AlgebraicClosure K` into `AlgebraicClosure K_v`.
- `autCongr_decompositionHom` (theorem): Transport of a decomposition homomorphism along an isomorphism `f : A ≃ₐ[K] Ω`.
- `apply_quotientMap_autCongr_localToGlobalGalois` (theorem): **The local Galois groups of `ι` and of Mathlib's embeddings.** A homomorphism from `G_S` to a commutative group takes the same value at the localization `localizationHom ι S v σ` and at `σ` mapped by `localToGlobalGalois v` and carried to `Gal(Ω / K)` by any isomorphism `f : AlgebraicClosure K ≃ₐ[K] Ω`: the two embeddings of `Ω` into `AlgebraicClosure K_v` differ by an automorphism of `Ω`, which conjugates the decomposition homomorphisms.
- `continuousCharEquivSIdeleClass_sPresentation_one_single_of_isArithmeticArtinLift` (theorem): **The character of the `S`-idèle class group at a place outside `S`, by local class field theory.** For a continuous character `χ` of `G_S` with values in `ℤ/n`, a finite place `v ∉ S` and an arithmetic Artin lift `σ` (of local class field theory) of the uniformizer `localUniformizer v`, the character `continuousCharEquivSIdeleClass χ` of the `S`-idèle class group takes at the generator of the divisors prime to `S` at `v` the value `χ(σ)⁻¹`, `σ` mapped to `G_S` by the localization `localizationHom ι S v`.

## References

- J. Neukirch, *Algebraic Number Theory* (Springer, 1999), Chapter V, §1, pp. 320–321 (the Frobenius automorphism `x ↦ x^q` of the maximal unramified
  extension; Theorem (1.3), the local reciprocity law, with the description of `r_{L|K}`: an
  extension of `σ` acting as `φ^n` on the maximal unramified extension, with fixed field `Σ`, goes to
  the norm of a prime element of `Σ`; for `L|K` unramified a prime element goes to the Frobenius);
  Chapter VI, Proposition (5.6), p. 391 (compatibility of the global and local norm residue symbols).
