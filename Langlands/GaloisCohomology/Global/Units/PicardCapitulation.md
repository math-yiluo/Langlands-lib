# `H¹(G_S, 𝒪_Sˣ) = Pic(𝒪_S)` for every `S`, by the principal ideal theorem

`Langlands/GaloisCohomology/Global/Units/PicardCapitulation.lean`, namespace `Langlands.GaloisCohomology`.

Let `F` be a number field, `S` a set of finite places of `F`, and `Ω / F` a separably closed Galois
extension. The module `Langlands.GaloisCohomology.Global.Units.Picard` defines an injection
`cohomologyOneSUnitsToSPicard : H¹(G_S, 𝒪_Sˣ) → Pic(𝒪_S)`. This file proves that it is onto for
every `S` (`cohomologyOneSUnitsToSPicard_surjective`), hence an isomorphism
`cohomologyOneSUnitsPicardEquiv : H¹(G_S, 𝒪_Sˣ) ≃+ Pic(𝒪_S)` (NSW (8.3.11) (ii)). The module
`Picard` also has `cohomologyOneSUnitsEquiv`, defined when the order of `Pic(𝒪_S)` is invertible
outside `S`; where it is defined, it is the equivalence of this file
(`cohomologyOneSUnitsEquiv_eq_cohomologyOneSUnitsPicardEquiv`).

The map sends the class of an `S`-invariant unit of `K_S` to the class of its divisor `divAbove`.
So the statement amounts to this: every divisor prime to `S` is the divisor of an `S`-invariant
unit of `K_S` (`divAbove_surjective`). In other words, every ideal class of `𝒪_S` becomes principal
in `K_S`. This is a capitulation statement. It follows from the principal ideal theorem,
`exists_unramified_extension_forall_isPrincipal` of the module
`Langlands.ClassFieldTheory.Global.Artin.PrincipalIdeal`: every number field has a finite extension,
unramified at every finite place, in which all its ideals become principal (the Hilbert class
field). Such an extension embeds into `K_S` over `F` (`nonempty_algHom_maximalUnramifiedOutside`
of the module `Langlands.Galois.RestrictedRamification.MaximalExtension`).

The proof uses three lemmas of the modules this file imports. `S`-units are `S`-invariant
(`isSInvariant_of_mem_maximalSUnits`), and a unit with an `S`-invariant power `x ^ N`, `N ≠ 0`, is
`S`-invariant (`isSInvariant_of_isSInvariant_pow`), both of the module
`Langlands.GaloisCohomology.Global.Units.Divisor`. If `x ^ N` is a unit `a` of `F` times an
`S`-unit, then `N • divAbove(x) = sDivisorOf(a)` (`nsmul_divAbove_eq_sDivisorOf` of the module
`Langlands.GaloisCohomology.Global.Units.Picard`). With the `S`-unit equal to `1`, this is the
identity that Kummer capitulation (`exists_divAbove_eq` of the module
`Langlands.GaloisCohomology.Global.Units.Divisor`) establishes for an `N`-th root `x` of `a`.

The same capitulation holds at every finite level of `K_S`, and gives back the surjectivity: the
module `Langlands.GaloisCohomology.Global.Units.CapitulationPrincipalIdeal` proves that every divisor
prime to `S` of a finite Galois subextension of `K_S` is the divisor of a unit of a larger one, so
that the divisor map of `K_S` is onto (`unitsToSDivisor_surjective`), and derives the surjectivity of
`cohomologyOneSUnitsToSPicard` from that (`cohomologyOneSUnitsToSPicard_surjective_of_surjective`).

The file imports the NYLL library (the copy under `Nyll/`) through
`Langlands.ClassFieldTheory.Global.Artin.PrincipalIdeal`, and so does every file that imports it.
Such a file inherits NYLL's global instances and `simp` lemmas (described on the page of that
module). This file declares no instance and no `simp` lemma.

## Complete types

```lean
@Langlands.GaloisCohomology.exists_divAbove_eq_single : ∀ {F Ω : Type u_1} [inst : Field F] [inst_1 : NumberField F]
  [inst_2 : Field Ω] [inst_3 : Algebra F Ω] [inst_4 : IsGalois F Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) [IsSepClosed Ω] (v : { v // v ∉ S }),
  ∃ x, (Langlands.GaloisCohomology.divAbove S) (Additive.ofMul x) = Finsupp.single v 1

@Langlands.GaloisCohomology.divAbove_surjective : ∀ {F Ω : Type u_1} [inst : Field F] [inst_1 : NumberField F]
  [inst_2 : Field Ω] [inst_3 : Algebra F Ω] [inst_4 : IsGalois F Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) [IsSepClosed Ω],
  Function.Surjective ⇑(Langlands.GaloisCohomology.divAbove S)

@Langlands.GaloisCohomology.cohomologyOneSUnitsToSPicard_surjective : ∀ {F Ω : Type u_1} [inst : Field F]
  [inst_1 : NumberField F] [inst_2 : Field Ω] [inst_3 : Algebra F Ω] [inst_4 : IsGalois F Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) [IsSepClosed Ω],
  Function.Surjective ⇑(Langlands.GaloisCohomology.cohomologyOneSUnitsToSPicard S)

@Langlands.GaloisCohomology.cohomologyOneSUnitsPicardEquiv : {F Ω : Type u_1} →
  [inst : Field F] →
    [inst_1 : NumberField F] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra F Ω] →
          [inst_4 : IsGalois F Ω] →
            (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) →
              [IsSepClosed Ω] →
                ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.maximalSUnitsModule F Ω S) 1) ≃+
                  Langlands.GaloisCohomology.SPicardGroup S

@Langlands.GaloisCohomology.cohomologyOneSUnitsPicardEquiv_apply : ∀ {F Ω : Type u_1} [inst : Field F]
  [inst_1 : NumberField F] [inst_2 : Field Ω] [inst_3 : Algebra F Ω] [inst_4 : IsGalois F Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) [inst_5 : IsSepClosed Ω]
  (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.maximalSUnitsModule F Ω S) 1)),
  (Langlands.GaloisCohomology.cohomologyOneSUnitsPicardEquiv S) x =
    (Langlands.GaloisCohomology.cohomologyOneSUnitsToSPicard S) x

@Langlands.GaloisCohomology.cohomologyOneSUnitsEquiv_eq_cohomologyOneSUnitsPicardEquiv : ∀ {F Ω : Type u_1}
  [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field Ω] [inst_3 : Algebra F Ω] [inst_4 : IsGalois F Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) [inst_5 : IsSepClosed Ω]
  (hS : ∀ v ∉ S, ↑(Nat.card (Langlands.GaloisCohomology.SPicardGroup S)) ∉ v.asIdeal),
  Langlands.GaloisCohomology.cohomologyOneSUnitsEquiv S hS = Langlands.GaloisCohomology.cohomologyOneSUnitsPicardEquiv S
```

## Outline of the proofs

*Three general steps*, lemmas of the imported modules whose proofs are on their pages:
`S`-invariance of a unit with an `S`-invariant power (`isSInvariant_of_isSInvariant_pow`, through
`mem_sUnitsOf_of_pow_mem`); the divisor of `x` with `x^N = a y`, `y` an `S`-unit
(`nsmul_divAbove_eq_sDivisorOf`: `divAbove` is a homomorphism on the `S`-invariant units, equal to
`sDivisorOf` on `Fˣ` and zero on `S`-units); and the embedding over `F` into `K_S` of a finite
extension `H / F` unramified outside `S` (`nonempty_algHom_maximalUnramifiedOutside`: the image of
an `F`-embedding `H → Ω` is unramified outside `S`, hence contained in `K_S`). No valuation is
computed in this file.

*A prime outside `S`.* Let `v ∉ S` and let `h` be the class number of `F`. Take `a ∈ 𝓞 F` with
`v^h = (a)`; it is the element behind `placeUnit v` (`exists_pow_classNumber_eq_span`). Let `H` be
the extension of the principal ideal theorem, with `v 𝓞_H = (α)`. Then
`(α^h) = (v 𝓞_H)^h = (a) 𝓞_H`, so `α^h u = a` for a unit `u` of `𝓞 H`
(`Ideal.span_singleton_eq_span_singleton`). Map `α` and `u` into `K_S` along the embedding. The
image `y` of `u` is an `S`-unit, because `u` and `u⁻¹` are integral over `ℤ`. So `x^h = a y⁻¹`
for the image `x` of `α`. By the two steps above, `x` is `S`-invariant and
`h • divAbove(x) = sDivisorOf(placeUnit v) = h • v` (`sDivisorOf_placeUnit`). Divisors form a
torsion-free group, so `divAbove(x) = v`.

*Surjectivity and the isomorphism.* `divAbove` is additive and the divisors `v` generate
(`Finsupp.induction_linear`), so `divAbove` is onto. A class of `Pic(𝒪_S)` is the class of a
divisor `D = divAbove(x)`, and it is the image of the class of `x`
(`cohomologyOneSUnitsToSPicard_apply`). With `cohomologyOneSUnitsToSPicard_injective` this gives
the isomorphism.

## Declarations

`exists_divAbove_eq_single`, `divAbove_surjective`, `cohomologyOneSUnitsToSPicard_surjective`,
`cohomologyOneSUnitsPicardEquiv`, `cohomologyOneSUnitsPicardEquiv_apply`,
`cohomologyOneSUnitsEquiv_eq_cohomologyOneSUnitsPicardEquiv`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition, corrected
  printing (Springer 2013): chapter VIII, §3, Proposition (8.3.11) (ii), p. 458
  (`H¹(G_S, 𝒪_Sˣ) ≅ Cl_S(k)`). The book proves it through the `S`-idèle class group: the proof of
  Proposition (8.3.6) (i), p. 456, uses that `lim Cl_S(K) = 0` over the finite subextensions of
  `k_S`, by the principal ideal theorem. In the book `S` contains the archimedean primes and `k_S`
  is unramified outside `S` (p. 452). The `S` of this file is a set of finite places, and `K_S`
  may ramify at the real places, so it is the book's `k_{S ∪ S_∞}`; `Pic(𝒪_S)` is the book's
  `Cl_{S ∪ S_∞}(k)`.
- J. Neukirch, *Algebraic Number Theory*, Grundlehren 322 (Springer 1999): chapter VI, §7,
  (7.5) Theorem, p. 410 (the principal ideal theorem).
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006): chapter I, §4,
  Proposition 4.3, p. 50. Its proof shows `lim Id_{F,S} = 0` over the finite subextensions of
  `K_S`, by the principal ideal theorem (Artin–Tate XIII 4).
