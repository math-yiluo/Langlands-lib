# The Euler characteristic formula for `ℓ`-primary modules, from Tate's base case

`Langlands/GaloisCohomology/Global/EulerCharacteristic/Internal/Primary.lean`, namespace `Langlands.GaloisCohomology`.

Let `K` be a number field, `Ω` a separable closure, `S` a finite set of finite places, `ℓ` a prime
with the places above `ℓ` in `S`, and `G_S` the Galois group of `K_S ⊆ Ω`.

**Tate's base case** (`GlobalEulerCharacteristicBaseStatement`): the formula holds for a finite module
`M` killed by `ℓ` when `G_S(L)` acts trivially on `M` for a finite Galois extension `L ⊆ K_S` of `K` of
degree prime to `ℓ` containing a primitive `ℓ`-th root of unity, with `ℓ` odd or `L` totally complex.

This file proves, assuming the base case, the formula for every finite module killed by a power of
`ℓ` (`globalEulerRatio_eq_one_of_primary_of_base`); Tate's theorem on the real places in degree three
(`realLocalizationDegreeThreeStatement`) enters through the multiplicativity of the ratio
(`globalEulerRatio_shortExact`):

* a module killed by `ℓ` is trivial on `G_S(L)` for a finite Galois `L ⊆ K_S` containing `μ_ℓ` (and `i`
  when `ℓ = 2`, so that `L` is totally complex) (`exists_splitting_field`);
* by the reduction to cyclic quotients (`globalEulerRatio_eq_one_of_cyclic`) and to their parts of
  degree prime to `ℓ` (`globalEulerRatio_coind_eq_one`) it suffices to know the formula over the fields
  `K''` with `K ⊆ K'' ⊆ L`, `[L : K'']` prime to `ℓ`, for `M` as a `G_S(K'')`-module, which is the base
  case over `K''` with `S_{K''}` the places above `S` (`globalEulerRatio_resToFixedField_eq_one`);
* the formula for modules killed by `ℓ` gives it for modules killed by `ℓ^r`
  (`globalEulerRatio_eq_one_of_primary`).

```lean
def GlobalEulerCharacteristicBaseStatement : Prop
theorem globalEulerRatio_resToFixedField_eq_one (hbase : GlobalEulerCharacteristicBaseStatement.{u})
    {ℓ : ℕ} [Fact ℓ.Prime]
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (L : IntermediateField K Ω) [NumberField L]
    (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S)
    [hN : (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).Normal]
    (hζ : ∃ ζ : L, IsPrimitiveRoot ζ ℓ) (hc : ℓ ≠ 2 ∨ IsTotallyComplex L)
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    (hℓM : ∀ m : M, ℓ • m = 0)
    (htriv : ∀ g ∈ (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)), M.ρ g = 1)
    (K'' : IntermediateField K Ω) [NumberField K'']
    (hK'' : ∀ x : K'', algebraMap K'' Ω x ∈ maximalUnramifiedOutside K Ω S)
    (hle : (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)) ≤
      GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hK'')
    (hcop : Nat.Coprime ((GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subgroupOf
      (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hK'' :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S))).index ℓ)
    (ιK'' : PlaceEmbeddings K'' Ω) :
    globalEulerRatio ιK'' (resToFixedField hK'' M) = 1
theorem exists_splitting_field {ℓ : ℕ} [hℓ : Fact ℓ.Prime]
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M] :
    ∃ (L : IntermediateField K Ω) (_ : NumberField L)
      (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S),
      (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).Normal ∧ (∃ ζ : L, IsPrimitiveRoot ζ ℓ) ∧
      (ℓ ≠ 2 ∨ IsTotallyComplex L) ∧
      ∀ g ∈ (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)), M.ρ g = 1
theorem globalEulerRatio_eq_one_of_primary_of_base
    (hbase : GlobalEulerCharacteristicBaseStatement.{u}) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    {r : ℕ} (hr : ∀ m : M, (ℓ ^ r) • m = 0) : globalEulerRatio ι M = 1
theorem globalEulerRatio_eq_one_of_base
    (hbase : GlobalEulerCharacteristicBaseStatement.{u})
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card M : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    globalEulerRatio ι M = 1
```

## Complete types

In the `#check @c` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.GlobalEulerCharacteristicBaseStatement : Prop
@Langlands.GaloisCohomology.globalEulerRatio_resToFixedField_eq_one : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S],
  Langlands.GaloisCohomology.GlobalEulerCharacteristicBaseStatement →
    ∀ {ℓ : ℕ} [Fact (Nat.Prime ℓ)],
      (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
        ∀ (L : IntermediateField K Ω) [inst_7 : NumberField ↥L]
          (hL : ∀ (x : ↥L), (algebraMap (↥L) Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
          [hN : (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).Normal],
          (∃ (ζ : ↥L), IsPrimitiveRoot ζ ℓ) →
            ℓ ≠ 2 ∨ NumberField.IsTotallyComplex ↥L →
              ∀ (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
                [inst_8 : Langlands.IsSmoothRep M] [Finite ↑M],
                (∀ (m : ↑M), ℓ • m = 0) →
                  (∀ g ∈ ↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL), M.ρ g = 1) →
                    ∀ (K'' : IntermediateField K Ω) [inst_10 : NumberField ↥K'']
                      (hK'' : ∀ (x : ↥K''), (algebraMap (↥K'') Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S),
                      ↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL) ≤
                          ↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hK'') →
                        ((↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subgroupOf
                                  ↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S
                                      hK'')).index.Coprime
                            ℓ →
                          ∀ (ιK'' : Langlands.Galois.PlaceEmbeddings (↥K'') Ω),
                            Langlands.GaloisCohomology.globalEulerRatio ιK''
                                (Langlands.GaloisCohomology.resToFixedField hK'' M) =
                              1
@Langlands.GaloisCohomology.exists_splitting_field : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
    ∀ (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
      [Langlands.IsSmoothRep M] [Finite ↑M],
      ∃ (L : IntermediateField K Ω) (x : NumberField ↥L) (hL :
        ∀ (x : ↥L), (algebraMap (↥L) Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S),
        (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).Normal ∧
          (∃ (ζ : ↥L), IsPrimitiveRoot ζ ℓ) ∧
            (ℓ ≠ 2 ∨ NumberField.IsTotallyComplex ↥L) ∧
              ∀ g ∈ ↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL), M.ρ g = 1
@Langlands.GaloisCohomology.globalEulerRatio_eq_one_of_primary_of_base : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω),
  Langlands.GaloisCohomology.GlobalEulerCharacteristicBaseStatement →
    ∀ {ℓ : ℕ},
      Nat.Prime ℓ →
        (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
          ∀ (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
            [inst_6 : Langlands.IsSmoothRep M] [Finite ↑M] {r : ℕ},
            (∀ (m : ↑M), ℓ ^ r • m = 0) → Langlands.GaloisCohomology.globalEulerRatio ι M = 1
@Langlands.GaloisCohomology.globalEulerRatio_eq_one_of_base : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω),
  Langlands.GaloisCohomology.GlobalEulerCharacteristicBaseStatement →
    ∀ (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
      [inst_6 : Langlands.IsSmoothRep M] [Finite ↑M],
      (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑(Nat.card ↑M) ∈ v.asIdeal → v ∈ S) →
        Langlands.GaloisCohomology.globalEulerRatio ι M = 1
```

## Outline of the proofs

Choose `L` trivializing `M` and containing `μ_ℓ` (and `i` for `ℓ = 2`), reduce to cyclic quotients (`Cyclic`) and to the parts of degree prime to `ℓ` (`Reduction`), which are instances of the base case over intermediate fields; the dévissage `0 → M[ℓ] → M → ℓM → 0` passes from modules killed by `ℓ` to modules killed by `ℓ^r`, and the primary decomposition by induction on `#M` (`0 → M[m] → M → mM → 0`) to all finite modules.

- `GlobalEulerCharacteristicBaseStatement`: **Tate's base case** of the global Euler characteristic formula: for every number field `K`, separable closure `Ω`, finite set `S` of finite places, prime `ℓ` with the places above `ℓ` in `S`, finite Galois extension `L ⊆ K_S` of `K` of degree prime to `ℓ` containing a primitive `ℓ`-th root of unity, with `ℓ` odd or `L` totally complex, and finite smooth `G_S`-module `M` killed by `ℓ` on which `G_S(L)` acts trivially, the ratio `globalEulerRatio ι M` is `1`.
- `globalEulerRatio_resToFixedField_eq_one`: **The base case over an intermediate field.** Let `L ⊆ K_S` be finite Galois over `K` with the properties of the base case except the degree, `M` a module killed by `ℓ` on which `G_S(L)` acts trivially, and `K ⊆ K'' ⊆ K_S` with `G_S(L) ⊆ G_S(K'')` of index prime to `ℓ`. Then the formula holds for `M` as a `G_{S_{K''}}(K'')`-module.
- `exists_splitting_field`: **A splitting field.** For a finite smooth `G_S`-module `M` and a prime `ℓ` with the places above `ℓ` in `S`, there is a finite Galois extension `L ⊆ K_S` of `K` containing a primitive `ℓ`-th root of unity, totally complex if `ℓ = 2`, such that `G_S(L)` acts trivially on `M`.
- `globalEulerRatio_eq_one_of_primary_of_base`: **The global Euler characteristic formula for `ℓ`-primary modules**, from the base case: for a finite smooth module `M` killed by a power of a prime `ℓ` with the places above `ℓ` in `S`, `globalEulerRatio ι M = 1`.
- `globalEulerRatio_eq_one_of_base`: **The global Euler characteristic formula for all finite modules**, from the base case: by the decomposition `0 → M[m] → M → mM → 0` with `#M = ℓ^a m`, `ℓ ∤ m`, into a module of smaller order and an `ℓ`-primary module, and multiplicativity.

## Declarations

`GlobalEulerCharacteristicBaseStatement`, `exists_eq_embedding_of_forall_fixingOpenSubgroup`, `le_of_fixingOpenSubgroup_le`, `isTotallyComplex_of_sq_eq_neg_one`, `algebraMap_mem_maximalUnramifiedOutside_over`, `globalEulerRatio_resToFixedField_eq_one`, `isOpen_ker_of_finite`, `exists_splitting_field`, `globalEulerRatio_eq_one_of_nsmul_of_base`, `globalEulerRatio_eq_one_of_primary_of_base`, `not_dvd_card_of_nsmul`, `globalEulerRatio_eq_one_of_base`.

## References

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed. (Springer 2008, corrected printing 2013), proof of (8.7.4), pp. 507–508 (reduction to modules killed by a prime p, and to a finite extension trivializing A).

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/Development/WeilBound/CoreStatements/PublishedTheorems/GlobalEulerCharacteristic/WorkSplit.lean` lines 1–120, `src/Development/WeilBound/CoreStatements/PublishedTheorems/GlobalEulerCharacteristic/WorkAssemble.lean` lines 1–48, `src/Development/WeilBound/CoreStatements/PublishedTheorems/GlobalEulerCharacteristic/RatioOneKilled.lean` lines 1–23. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's cohomology API replaces the source's: `map φ f n`, `coeffMap`, `res`, `IsSmoothRep` for the source's `cohomologyMapAlong`, `cohomologyMap`, `cohomologyRes`, `IsDiscreteRep`; `G_S`, its localizations and the open subgroups `G_S(L)` are the Library's `GaloisGroupUnramifiedOutside`, `localizationHom`, `realLocalizationHom`, `fixingOpenSubgroup` in place of the source's `galUnramifiedOutside`, `gsFinFamily`, `gsRealFamily`, `gsOpenSubgroup` (over `FiniteSubfield`s of `ℚ̄`).

Renamings (source → Library): `exists_split` → `exists_splitting_field`, `ratio_eq_one_of_coprime_cyclic'` → `globalEulerRatio_resToFixedField_eq_one`, `ratioOneKilled_two` → `globalEulerRatio_eq_one_of_nsmul_of_base`, `ratioOneKilled_of_lemmaX` → `globalEulerRatio_eq_one_of_primary_of_base`.
