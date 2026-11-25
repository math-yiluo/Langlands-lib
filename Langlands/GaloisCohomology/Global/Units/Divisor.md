# Divisors prime to `S`, and the divisor of an `S`-invariant unit of `K_S`

`Langlands/GaloisCohomology/Global/Units/Divisor.lean`, namespace `Langlands.GaloisCohomology`.

For a number field `F` and a set `S` of finite places, `SDivisor S` is the group of divisors prime
to `S` (finitely supported functions from the finite places outside `S` to `ℤ`) and
`sDivisorOf S : Fˣ → SDivisor S` sends `x` to `v ↦ ord_v(x)` (`ordAt`, the negative logarithm of
the `v`-adic valuation).

For a Galois extension `Ω / F` and the maximal extension `K_S ⊆ Ω` unramified outside `S`, a unit
`x` of `K_S` is `S`-invariant (`IsSInvariant`) when `σ(x)/x` is an `S`-unit for all `σ ∈ G_S`; these
form the subgroup `sInvariantSubgroup Ω S`, which contains `Fˣ` and the `S`-units of `K_S`
(`isSInvariant_of_mem_maximalSUnits`). A unit with an `S`-invariant power `x ^ N`, `N ≠ 0`, is
`S`-invariant (`isSInvariant_of_isSInvariant_pow`). For `v ∉ S`, all places above `v`
of a finite Galois subextension `M ⊆ K_S` containing `x` give `x` the same valuation
(`valuation_eq_of_isSInvariant`: `G_S` acts transitively on them and the `S`-unit `σ(x)/x` has
valuation `1` there), and the common value does not depend on `M` (places extend to larger
subextensions with the same valuations, which are unramified above `v`). This is `ordAbove v x`
(`IsOrdAbove.unique`, `valuation_eq_exp_ordAbove`), and `divAbove S x` is the divisor
`v ↦ ordAbove v x` prime to `S` (finitely supported: `finite_ordAbove_ne_zero`).

- On `Fˣ`, `divAbove` is `sDivisorOf` (`divAbove_algebraMap`).
- An `S`-invariant unit with divisor zero is an `S`-unit of `K_S`
  (`mem_maximalSUnits_of_divAbove_eq_zero`).
- Capitulation by Kummer theory (`exists_divAbove_eq`): if `N` is invertible outside `S`, `Ω` is
  separably closed and `N • D = sDivisorOf S a`, then any `N`-th root `x` of `a` lies in `K_S`, is
  `S`-invariant, and `divAbove S x = D`.

## Complete types

```lean
@Langlands.GaloisCohomology.SDivisor : {F : Type u_1} →
  [inst : Field F] → Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) → Type u_1

@Langlands.GaloisCohomology.sDivisorOf : {F : Type u_1} →
  [inst : Field F] →
    [NumberField F] →
      (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) →
        Additive Fˣ →+ Langlands.GaloisCohomology.SDivisor S

@Langlands.GaloisCohomology.IsSInvariant : {F Ω : Type u_1} →
  [inst : Field F] →
    [NumberField F] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra F Ω] →
          (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) →
            (↥(Langlands.Galois.maximalUnramifiedOutside F Ω S))ˣ → Prop

@Langlands.GaloisCohomology.isSInvariant_of_mem_maximalSUnits : ∀ {F Ω : Type u_1} [inst : Field F]
  [inst_1 : NumberField F] [inst_2 : Field Ω] [inst_3 : Algebra F Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)))
  {y : (↥(Langlands.Galois.maximalUnramifiedOutside F Ω S))ˣ},
  y ∈ Langlands.GaloisCohomology.maximalSUnits F Ω S → Langlands.GaloisCohomology.IsSInvariant S y

@Langlands.GaloisCohomology.isSInvariant_of_isSInvariant_pow : ∀ {F Ω : Type u_1} [inst : Field F]
  [inst_1 : NumberField F] [inst_2 : Field Ω] [inst_3 : Algebra F Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)))
  {x : (↥(Langlands.Galois.maximalUnramifiedOutside F Ω S))ˣ} {N : ℕ},
  N ≠ 0 → Langlands.GaloisCohomology.IsSInvariant S (x ^ N) → Langlands.GaloisCohomology.IsSInvariant S x

@Langlands.GaloisCohomology.ordAbove : {F Ω : Type u_1} →
  [inst : Field F] →
    [NumberField F] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra F Ω] →
          [IsGalois F Ω] →
            (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) →
              IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) →
                (↥(Langlands.Galois.maximalUnramifiedOutside F Ω S))ˣ → ℤ

@Langlands.GaloisCohomology.divAbove : {F Ω : Type u_1} →
  [inst : Field F] →
    [inst_1 : NumberField F] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra F Ω] →
          [IsGalois F Ω] →
            (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) →
              Additive ↥(Langlands.GaloisCohomology.sInvariantSubgroup Ω S) →+ Langlands.GaloisCohomology.SDivisor S

@Langlands.GaloisCohomology.divAbove_algebraMap : ∀ {F Ω : Type u_1} [inst : Field F] [inst_1 : NumberField F]
  [inst_2 : Field Ω] [inst_3 : Algebra F Ω] [inst_4 : IsGalois F Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) (a : Fˣ),
  (Langlands.GaloisCohomology.divAbove S)
      (Additive.ofMul ⟨(Units.map ↑(algebraMap F ↥(Langlands.Galois.maximalUnramifiedOutside F Ω S))) a, ⋯⟩) =
    (Langlands.GaloisCohomology.sDivisorOf S) (Additive.ofMul a)

@Langlands.GaloisCohomology.mem_maximalSUnits_of_divAbove_eq_zero : ∀ {F Ω : Type u_1} [inst : Field F]
  [inst_1 : NumberField F] [inst_2 : Field Ω] [inst_3 : Algebra F Ω] [inst_4 : IsGalois F Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)))
  {x : ↥(Langlands.GaloisCohomology.sInvariantSubgroup Ω S)},
  (Langlands.GaloisCohomology.divAbove S) (Additive.ofMul x) = 0 → ↑x ∈ Langlands.GaloisCohomology.maximalSUnits F Ω S

@Langlands.GaloisCohomology.exists_divAbove_eq : ∀ {F Ω : Type u_1} [inst : Field F] [inst_1 : NumberField F]
  [inst_2 : Field Ω] [inst_3 : Algebra F Ω] [inst_4 : IsGalois F Ω] [IsSepClosed Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) {N : ℕ},
  N ≠ 0 →
    (∀ v ∉ S, ↑N ∉ v.asIdeal) →
      ∀ (D : Langlands.GaloisCohomology.SDivisor S) (a : Fˣ),
        (Langlands.GaloisCohomology.sDivisorOf S) (Additive.ofMul a) = N • D →
          ∃ (x : ↥(Langlands.GaloisCohomology.sInvariantSubgroup Ω S)),
            (Langlands.GaloisCohomology.divAbove S) (Additive.ofMul x) = D
```

## Outline of the proofs

`S`-units are `S`-invariant because `G_S` maps `S`-units to `S`-units (`galUnitsHom_mem_sUnitsOf`).
If `x ^ N` is `S`-invariant, `(σx/x)^N = σ(x^N)/x^N` is an `S`-unit, hence so is `σx/x`
(`mem_sUnitsOf_of_pow_mem`: `S`-units are defined by integrality, and a unit whose power is
integral is integral).

Transitivity of `Gal(M/F)` on the places above `v` comes from Mathlib's `IsGaloisGroup` for the
rings of integers. The comparison of valuations along `M ⊆ M'` uses that the places above `v ∉ S`
are unramified in `K_S` (`valuation_algebraMap_of_isUnramifiedAt` of
`Langlands/Galois/RestrictedRamification/Unramified.lean`). In `exists_divAbove_eq` the root `x`
lies in `K_S` by `mem_maximalUnramifiedOutside_of_pow_eq` (an `N`-th root of the `S`-unit `a`
outside the support of `D`, after the Kummer lemma of `SUnits.lean`), `σ(x)/x` is a root of unity,
and `N · ordAbove v x = ord_v(a) = N · D(v)`.

## Declarations

`ordAt`, `ordAt_mul`, `ordAt_one`, `ordAt_inv`, `ordAt_eq_zero_iff`, `valuation_eq_exp_neg_ordAt`,
`finite_ordAt_ne_zero`, `SDivisor`, `sDivisorOf`, `sDivisorOf_apply`, `exists_under_eq`,
`under_under_of_tower`, `valuation_algebraMap_under`, `IsSInvariant`,
`isSInvariant_of_mem_maximalSUnits`, `isSInvariant_of_isSInvariant_pow`, `IsOrdAbove`,
`exists_isOrdAbove`, `exists_galoisGroupUnramifiedOutside_restrict`,
`valuation_eq_of_isSInvariant`, `finiteDimensional_of_numberField`,
`exists_place_valuation_eq_of_le`, `IsOrdAbove.unique`, `ordAbove`, `isOrdAbove_ordAbove`,
`ordAbove_eq_of_isOrdAbove`, `valuation_eq_exp_ordAbove`, `galUnitsHom_mul_inv_eq`,
`sInvariantSubgroup`, `mem_sInvariantSubgroup`, `map_algebraMap_mem_sInvariantSubgroup`,
`exists_numberField_mem`, `finite_ordAbove_ne_zero`, `ordAbove_one`, `ordAbove_mul`, `divAbove`,
`divAbove_apply`, `mem_maximalSUnits_of_divAbove_eq_zero`, `divAbove_algebraMap`,
`exists_divAbove_eq`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files
`src/GroundTheory/ProfiniteCohomology/RestrictedRamification/SPicDefs.lean` (lines 8–67, without the
quotient `sPic`) and `src/GroundTheory/ProfiniteCohomology/RestrictedRamification/SDivisor.lean`
(lines 15–475). The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Changes: `sDivisor`, `divS`,
`exists_underPlace_eq`, `underPlace_underPlace`, `valuation_algebraMap_underPlace`,
`mem_sUnitsMax_of_divAbove_eq_zero`, `exists_galUnramifiedOutside_restrict` are `SDivisor`,
`sDivisorOf`, `exists_under_eq`, `under_under_of_tower`, `valuation_algebraMap_under`,
`mem_maximalSUnits_of_divAbove_eq_zero`, `exists_galoisGroupUnramifiedOutside_restrict`; places
below are Mathlib's `HeightOneSpectrum.under`; `K_S`, `G_S` are Stage 1's
`maximalUnramifiedOutside`, `GaloisGroupUnramifiedOutside`. `isSInvariant_of_mem_maximalSUnits` and
`isSInvariant_of_isSInvariant_pow` are not from the source.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition, corrected
  printing (Springer 2013): chapter VIII, §3, Proposition (8.3.11) and its proof, p. 458 (there
  `H¹(G_S, 𝒪_Sˣ)` is computed through the `S`-idèles and `S`-idèle classes of `k_S`; here through the
  divisors of `S`-invariant units, the route of the source).
