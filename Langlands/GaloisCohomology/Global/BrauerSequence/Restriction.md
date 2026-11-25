# Restriction of global Brauer classes to finite extensions

`Langlands/GaloisCohomology/Global/BrauerSequence/Restriction.lean`, namespace
`Langlands.GaloisCohomology`.

**Finite level.** For number fields `F ⊆ K ⊆ L` with `L/F` Galois:
`finiteLocalInvariant_relativeRestriction`: for places `q | w | v` and a local invariant family with
the restriction law, the local invariant at `q` over `K` of the restriction of `c ∈ H²(Gal(L/F), Lˣ)`
is `[K_w : F_v]` times its local invariant at `q` over `F`;
`archimedeanInvariant_relativeRestriction_eq_zero`: if the archimedean invariant over `F` of `c` at an
infinite place `q` of `L` vanishes, so does the archimedean invariant over `K` of its restriction.

**Restriction and inflation.** For fields `K ⊆ E ⊆ L ⊆ Ω` with the Galois conditions:
`unitsRestriction_unitsTowerMap`: restriction to `Gal(Ω/E)` of a class inflated from `Gal(L/K)` is the
inflation from `Gal(L/E)` of its restriction; `unitsRestriction_isoGroupCohomology_inv`: at a finite
level the restriction of the cochain model is the Library's `relativeRestriction`.

**Restriction.** `brauerRestriction_eq_zero'`: a global Brauer class killed by `m` dies in every
finite extension `E ⊆ Ω` of `K` whose local degrees above the finite places where the class is
nonzero are multiples of `m`, provided its real localizations vanish at the real places of `K` below
a real place of `E`. With all real localizations zero this is the field `brauerRestriction_eq_zero`
of `BrauerSequenceData`; for `E` without real places the condition is empty
(`brauerRestriction_eq_zero_of_isComplex` of `Langlands.GaloisCohomology.Global.Units.ComplexRestriction`).

## Complete types

```lean
@Langlands.GaloisCohomology.finiteLocalInvariant_relativeRestriction : ∀ {F K L : Type u_1} [inst : Field F]
  [inst_1 : Field K] [inst_2 : Field L] [inst_3 : NumberField F] [inst_4 : NumberField K] [inst_5 : NumberField L]
  [inst_6 : Algebra F K] [inst_7 : Algebra K L] [inst_8 : Algebra F L] [inst_9 : IsScalarTower F K L]
  [inst_10 : IsGalois F L]
  (I : (p : ℕ) → [inst : Fact (Nat.Prime p)] → Langlands.ClassFieldTheory.Local.InvariantFamily p),
  (∀ (p : ℕ) [inst : Fact (Nat.Prime p)], (I p).RelativeRestriction) →
    ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
      (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
      (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) [inst_11 : w.asIdeal.LiesOver v.asIdeal]
      [inst_12 : q.asIdeal.LiesOver w.asIdeal] [inst_13 : q.asIdeal.LiesOver v.asIdeal]
      (c : ↑(Langlands.ClassFieldTheory.Local.relativeCohomology F L 2)),
      (Langlands.ClassFieldTheory.Global.Reciprocity.finiteLocalInvariant w q I)
          ((ModuleCat.Hom.hom (Langlands.ClassFieldTheory.Local.relativeRestriction F K L 2)) c) =
        Module.finrank (IsDedekindDomain.HeightOneSpectrum.adicCompletion F v)
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion K w) •
          (Langlands.ClassFieldTheory.Global.Reciprocity.finiteLocalInvariant v q I) c

@Langlands.GaloisCohomology.archimedeanInvariant_relativeRestriction_eq_zero : ∀ {F K L : Type u_1} [inst : Field F]
  [inst_1 : Field K] [inst_2 : Field L] [inst_3 : Algebra F K] [inst_4 : Algebra K L] [inst_5 : Algebra F L]
  [inst_6 : IsScalarTower F K L] [IsGalois F L] (q : NumberField.InfinitePlace L)
  (c : ↑(Langlands.ClassFieldTheory.Local.relativeCohomology F L 2)),
  (Langlands.ClassFieldTheory.Global.Reciprocity.archimedeanInvariant q) c = 0 →
    (Langlands.ClassFieldTheory.Global.Reciprocity.archimedeanInvariant q)
        ((ModuleCat.Hom.hom (Langlands.ClassFieldTheory.Local.relativeRestriction F K L 2)) c) =
      0

Langlands.GaloisCohomology.unitsRestriction_unitsTowerMap : ∀ (K E L Ω : Type u_1) [inst : Field K] [inst_1 : Field E]
  [inst_2 : Field L] [inst_3 : Field Ω] [inst_4 : Algebra K E] [inst_5 : Algebra K L] [inst_6 : Algebra K Ω]
  [inst_7 : Algebra E L] [inst_8 : Algebra E Ω] [inst_9 : Algebra L Ω] [inst_10 : IsScalarTower K E L]
  [inst_11 : IsScalarTower K E Ω] [inst_12 : IsScalarTower K L Ω] [inst_13 : IsScalarTower E L Ω]
  [inst_14 : IsGalois K Ω] [inst_15 : IsGalois E Ω] [inst_16 : IsGalois K L] [inst_17 : IsGalois E L]
  (y : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K L) 2)),
  (ModuleCat.Hom.hom (Langlands.GaloisCohomology.unitsRestriction K E Ω 2))
      ((ModuleCat.Hom.hom (Langlands.GaloisCohomology.unitsTowerMap K L Ω 2)) y) =
    (ModuleCat.Hom.hom (Langlands.GaloisCohomology.unitsTowerMap E L Ω 2))
      ((ModuleCat.Hom.hom (Langlands.GaloisCohomology.unitsRestriction K E L 2)) y)

Langlands.GaloisCohomology.unitsRestriction_isoGroupCohomology_inv : ∀ (K E L : Type u_1) [inst : Field K]
  [inst_1 : Field E] [inst_2 : Field L] [inst_3 : Algebra K E] [inst_4 : Algebra K L] [inst_5 : Algebra E L]
  [inst_6 : IsScalarTower K E L] [inst_7 : IsGalois K L] [inst_8 : IsGalois E L] [inst_9 : FiniteDimensional K L]
  [inst_10 : FiniteDimensional E L] (a : ↑(Langlands.ClassFieldTheory.Local.relativeCohomology K L 2)),
  (ModuleCat.Hom.hom (Langlands.GaloisCohomology.unitsRestriction K E L 2))
      ((ModuleCat.Hom.hom
          (Langlands.ProfiniteCohomology.isoGroupCohomology (Langlands.GaloisCohomology.unitsModule K L) 2).inv)
        a) =
    (ModuleCat.Hom.hom
        (Langlands.ProfiniteCohomology.isoGroupCohomology (Langlands.GaloisCohomology.unitsModule E L) 2).inv)
      ((ModuleCat.Hom.hom (Langlands.ClassFieldTheory.Local.relativeRestriction K E L 2)) a)

@Langlands.GaloisCohomology.brauerRestriction_eq_zero' : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (E : IntermediateField K Ω) [inst_5 : FiniteDimensional K ↥E]
  (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) 2)) (m : ℕ),
  m • x = 0 →
    (∀ (u : NumberField.InfinitePlace ↥E),
        u.IsReal → (Langlands.GaloisCohomology.realBrauerLocalization ι (u.comap (Algebra.algebraMap K ↥E)) 2) x = 0) →
      (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
          (Langlands.GaloisCohomology.brauerLocalization ι v 2) x ≠ 0 →
            ∀ (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥E))
              [inst_6 : w.asIdeal.LiesOver v.asIdeal], m ∣ Langlands.GaloisCohomology.localDegree E v w) →
        (Langlands.GaloisCohomology.brauerRestriction E) x = 0
```

## Outline of the proofs

`finiteLocalInvariant_relativeRestriction` follows the Library's
`finiteIdeleInvariantRestriction_of_relativeRestriction` with the units in place of the idèles: the
local component of the restriction is the local restriction of the local component
(`Reciprocity.unitsLocalMap_relativeRestriction`), and the restriction law of the family
(`RelativeRestriction`) applies to `K_v ⊆ E_w ⊆ L_q` through `towerPadicField`. The archimedean
statement compares `archimedeanCocycleHom` over `K` and over `F`: a nontrivial `d ∈ Gal(L/K)` fixing
`q` restricts to a nontrivial element of `Gal(L/F)` fixing `q`, with the same value `f(d, d) f(1, 1)`.
The compatibility of restriction and inflation is `map_comp` and `map_congr` of the foundations, the
two composite group homomorphisms `Gal(Ω/E) → Gal(L/K)` being equal. `brauerRestriction_eq_zero'`:
inflate the class from a
finite Galois level `L` containing `E` (the compositum of a level of the class and the normal closure
of `E`, `unitsInflationOfLE_comp_unitsInflation`); its restriction to `E` is the inflation of the
Library's restriction `b ∈ H²(Gal(L/E), Lˣ)`, and `b = 0` by the Library's Hasse principle for `L/E`:
the local invariants of `b` are `[E_u : K_v]` times local invariants of the class, which are killed
by `m` and zero where the class is locally zero; its archimedean invariant at an infinite place `q`
of `L` above a real place of `E` vanishes with the real localization of the class below `q`, and at
the other infinite places, unramified over `E` (Mathlib's `InfinitePlace.not_isUnramified_iff`), the
decomposition group of `q` in `Gal(L/E)` is trivial (`Reciprocity.archimedeanCocycleHom_apply_of_not_exists`).

## Declarations

`finiteLocalInvariant_relativeRestriction`, `archimedeanInvariant_relativeRestriction_eq_zero`,
`unitsRestriction_unitsTowerMap`, `unitsRestriction_isoGroupCohomology_inv`,
`brauerRestriction_eq_zero'`.

## Source and licence

New file; it contains no text of the repository `leanprover-community/riemann-hypothesis`. It replaces
the source's `unitsResField_eq_zero_of_dvd_finrank` (`GlobalClassFormation/Splitting.lean`), proved
there through the source's idèle class formation, by a proof from the Library's finite-level
theorems.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition, corrected
  printing (Springer 2013): Corollary (7.1.4), p. 375 (`inv_K ∘ res = [K : k] · inv_k`);
  Proposition (8.1.10), p. 432 (the same for the global invariant); Theorem (8.1.17), p. 437.
