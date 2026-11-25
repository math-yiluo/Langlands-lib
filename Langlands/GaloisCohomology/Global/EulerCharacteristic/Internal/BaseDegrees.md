# Tate's base case in degrees zero and one

`Langlands/GaloisCohomology/Global/EulerCharacteristic/Internal/BaseDegrees.lean`, namespace `Langlands.GaloisCohomology`.

Let `K` be a number field, `S` a finite set of finite places containing the places above the
prime `ℓ`, `L ⊆ K_S` finite Galois over `K` with `μ_ℓ ⊆ L` and `[L : K]` prime to `ℓ`, `P ⊆ G_S` the
subgroup fixing `L`, and `M` a `G_S`-module killed by `ℓ` on which `P` acts trivially. With
`d = baseTwistFun` the additive function `X ↦ dim (X ⊗ Hom(μ_ℓ, M))^{Gal(L/K)}` and
`Aᵢ = Hⁱ(P, 𝒪_Sˣ)`:

* `dim H⁰(G_S, M) = d(A₀[ℓ])` (`baseCase_finrank_zero`) and
  `dim H¹(G_S, M) = d(A₀/ℓ) + d(A₁[ℓ])` (`baseCase_finrank_one`), from the coprime twist and the
  Kummer sequence;
* `d(A₀/ℓ) - d(A₀[ℓ]) = d(𝔽_ℓ[S_L]) + d(𝔽_ℓ[∞_L]) - d(𝔽_ℓ)` (`baseCase_units`), from the `S`-units of
  `L` as a Galois lattice, and `d(A₁/ℓ) = d(A₁[ℓ])` since `A₁` is finite (`baseCase_picard`).

Together: `dim H⁰ - dim H¹ = d(𝔽_ℓ) - d(𝔽_ℓ[S_L]) - d(𝔽_ℓ[∞_L]) - d(A₁/ℓ)`
(`baseCase_finrank_zero_sub_finrank_one`).

```lean
theorem baseCase_finrank_zero :
    haveI
theorem baseCase_finrank_one :
    haveI
theorem baseCase_units (d : AdditiveFunction.{u} ℓ (L ≃ₐ[K] L)) :
    haveI
theorem baseCase_picard [IsGalois K L] (d : AdditiveFunction.{u} ℓ (L ≃ₐ[K] L)) :
    haveI
```

## Complete types

In the `#check @c` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.baseCase_finrank_zero : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [inst_5 : Finite ↑S] {ℓ : ℕ}
  [inst_6 : Fact (Nat.Prime ℓ)],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
    ∀ {L : Type u} [inst_7 : Field L] [inst_8 : NumberField L] [inst_9 : Algebra K L] [inst_10 : Algebra L Ω]
      [inst_11 : IsScalarTower K L Ω]
      (hL : ∀ (x : L), (algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) [inst_12 : IsGalois K L]
      [inst_13 : (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).Normal]
      (hcop : (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).index.Coprime ℓ)
      (hζ : ∃ (ζ : L), IsPrimitiveRoot ζ ℓ)
      (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
      [inst_14 : Langlands.IsSmoothRep M] [inst_15 : Finite ↑M] (hMℓ : ∀ (m : ↑M), ℓ • m = 0)
      (hMP : ∀ g ∈ ↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL), M.ρ g = 1),
      ↑(Module.finrank (ULift.{u, 0} (ZMod ℓ))
            ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.ProfiniteCohomology.zmodRepOfTorsion ℓ M hMℓ) 0)) =
        (Langlands.GaloisCohomology.baseTwistFun hL hcop hζ M hMℓ hMP).toFun
          (Langlands.GaloisCohomology.Local.TorsN
            (↑(Langlands.ProfiniteCohomology.cohomology
                (Rep.res (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype
                  (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S))
                0))
            ℓ)
          (Langlands.GaloisCohomology.Local.torsNRep Gal(L/K)
            (↑(Langlands.ProfiniteCohomology.cohomology
                (Rep.res (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype
                  (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S))
                0))
            ℓ)
@Langlands.GaloisCohomology.baseCase_finrank_one : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [inst_5 : Finite ↑S] {ℓ : ℕ}
  [inst_6 : Fact (Nat.Prime ℓ)],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
    ∀ {L : Type u} [inst_7 : Field L] [inst_8 : NumberField L] [inst_9 : Algebra K L] [inst_10 : Algebra L Ω]
      [inst_11 : IsScalarTower K L Ω]
      (hL : ∀ (x : L), (algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) [inst_12 : IsGalois K L]
      [inst_13 : (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).Normal]
      (hcop : (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).index.Coprime ℓ)
      (hζ : ∃ (ζ : L), IsPrimitiveRoot ζ ℓ)
      (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
      [inst_14 : Langlands.IsSmoothRep M] [inst_15 : Finite ↑M] (hMℓ : ∀ (m : ↑M), ℓ • m = 0)
      (hMP : ∀ g ∈ ↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL), M.ρ g = 1),
      ↑(Module.finrank (ULift.{u, 0} (ZMod ℓ))
            ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.ProfiniteCohomology.zmodRepOfTorsion ℓ M hMℓ) 1)) =
        (Langlands.GaloisCohomology.baseTwistFun hL hcop hζ M hMℓ hMP).toFun
            (ModN
              (↑(Langlands.ProfiniteCohomology.cohomology
                  (Rep.res (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype
                    (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S))
                  0))
              ℓ)
            (Langlands.GaloisCohomology.Local.modNRep Gal(L/K)
              (↑(Langlands.ProfiniteCohomology.cohomology
                  (Rep.res (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype
                    (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S))
                  0))
              ℓ) +
          (Langlands.GaloisCohomology.baseTwistFun hL hcop hζ M hMℓ hMP).toFun
            (Langlands.GaloisCohomology.Local.TorsN
              (↑(Langlands.ProfiniteCohomology.cohomology
                  (Rep.res (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype
                    (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S))
                  1))
              ℓ)
            (Langlands.GaloisCohomology.Local.torsNRep Gal(L/K)
              (↑(Langlands.ProfiniteCohomology.cohomology
                  (Rep.res (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype
                    (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S))
                  1))
              ℓ)
@Langlands.GaloisCohomology.baseCase_units : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [inst_5 : Finite ↑S] {ℓ : ℕ}
  [inst_6 : Fact (Nat.Prime ℓ)] {L : Type u} [inst_7 : Field L] [inst_8 : NumberField L] [inst_9 : Algebra K L]
  [inst_10 : Algebra L Ω] [inst_11 : IsScalarTower K L Ω]
  (hL : ∀ (x : L), (algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) [inst_12 : IsGalois K L]
  [inst_13 : (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).Normal]
  (d : Langlands.GaloisCohomology.Local.AdditiveFunction ℓ Gal(L/K)),
  d.toFun
        (ModN
          (↑(Langlands.ProfiniteCohomology.cohomology
              (Rep.res (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype
                (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S))
              0))
          ℓ)
        (Langlands.GaloisCohomology.Local.modNRep Gal(L/K)
          (↑(Langlands.ProfiniteCohomology.cohomology
              (Rep.res (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype
                (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S))
              0))
          ℓ) -
      d.toFun
        (Langlands.GaloisCohomology.Local.TorsN
          (↑(Langlands.ProfiniteCohomology.cohomology
              (Rep.res (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype
                (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S))
              0))
          ℓ)
        (Langlands.GaloisCohomology.Local.torsNRep Gal(L/K)
          (↑(Langlands.ProfiniteCohomology.cohomology
              (Rep.res (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype
                (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S))
              0))
          ℓ) =
    d.toFun (↑(Langlands.Galois.finitePlacesAbove L S) → ZMod ℓ)
          (Langlands.GaloisCohomology.funPermRep (ZMod ℓ) Gal(L/K) ↑(Langlands.Galois.finitePlacesAbove L S)) +
        d.toFun (NumberField.InfinitePlace L → ZMod ℓ)
          (Langlands.GaloisCohomology.funPermRep (ZMod ℓ) Gal(L/K) (NumberField.InfinitePlace L)) -
      d.one
@Langlands.GaloisCohomology.baseCase_picard : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {ℓ : ℕ} {L : Type u} [inst_5 : Field L]
  [inst_6 : NumberField L] [inst_7 : Algebra K L] [inst_8 : Algebra L Ω] [inst_9 : IsScalarTower K L Ω]
  (hL : ∀ (x : L), (algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  [inst_10 : (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).Normal] [inst_11 : IsGalois K L]
  (d : Langlands.GaloisCohomology.Local.AdditiveFunction ℓ Gal(L/K)),
  d.toFun
      (ModN
        (↑(Langlands.ProfiniteCohomology.cohomology
            (Rep.res (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype
              (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S))
            1))
        ℓ)
      (Langlands.GaloisCohomology.Local.modNRep Gal(L/K)
        (↑(Langlands.ProfiniteCohomology.cohomology
            (Rep.res (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype
              (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S))
            1))
        ℓ) =
    d.toFun
      (Langlands.GaloisCohomology.Local.TorsN
        (↑(Langlands.ProfiniteCohomology.cohomology
            (Rep.res (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype
              (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S))
            1))
        ℓ)
      (Langlands.GaloisCohomology.Local.torsNRep Gal(L/K)
        (↑(Langlands.ProfiniteCohomology.cohomology
            (Rep.res (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype
              (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S))
            1))
        ℓ)
```

## Outline of the proofs

Combine `TwistCount` (`dim Hⁱ(G, M) = d(Hⁱ(P, μ_ℓ))`) with `KummerCount` for the Kummer sequence of the `S`-units restricted to `P`: `h0 = d(A₀[ℓ])`, `h1 = d(A₀/ℓ) + d(A₁[ℓ])`; `UnitLattice` computes `d(A₀/ℓ) - d(A₀[ℓ])`, and `d(A₁/ℓ) = d(A₁[ℓ])` since `A₁` is finite.

- `baseCase_finrank_zero`: **Degree zero.** `dim H⁰(G_S, M) = d(A₀[ℓ])`.
- `baseCase_finrank_one`: **Degree one.** `dim H¹(G_S, M) = d(A₀/ℓ) + d(A₁[ℓ])`.
- `baseCase_units`: **The `S`-units.** `d(A₀/ℓ) - d(A₀[ℓ]) = d(𝔽_ℓ[S_L]) + d(𝔽_ℓ[∞_L]) - d(𝔽_ℓ)` for every additive function `d`.
- `baseCase_picard`: **The `S`-class group.** `A₁` is finite, so `d(A₁/ℓ) = d(A₁[ℓ])`.

## Declarations

`compactSpace_fixingOpenSubgroup`, `res_apply_eq_of_trivial`, `coprime_card_gal`, `moduleFinite_homRep_roots`, `baseTwistFun`, `index_ne_zero_zmod`, `baseKummer_shortExact`, `moduleFinite_cohomology_zero_res_maximalSUnits`, `baseCase_finrank_zero`, `baseCase_finrank_one`, `baseCase_units`, `baseCase_picard`.

## References

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed. (Springer 2008, corrected printing 2013), proof of (8.7.4), pp. 506–507 ((i)–(iii) and the functional Θ).
