# Totally complex quadratic extensions splitting Brauer classes killed by two

Module: `Langlands.GaloisCohomology.Global.BrauerSequence.QuadraticComplexSplitting`,
namespace `Langlands.GaloisCohomology`.

Over a number field `K`, every Brauer class killed by `2` dies in some quadratic
extension of `K` without real places. This module proves this for the Library's
Brauer group `H²(Gal(Ω/K), Ωˣ)` (`Ω` a separable closure of `K`) and then in the
relative form needed for unit-valued two-cocycles of finite Galois extensions.

## Main results

- `exists_quadratic_isComplex_brauerRestriction_eq_zero`: for `K, Ω : Type u` with
  `[NumberField K]` and `[IsSepClosure K Ω]`, and
  `x : cohomology (unitsModule K Ω) 2` with `2 • x = 0`, there is
  `E : IntermediateField K Ω` with `Module.finrank K E = 2`, every
  `u : InfinitePlace E` complex, and `brauerRestriction E x = 0`.
- `exists_quadratic_isComplex_relativeRestriction_eq_zero`: for a number field
  `F : Type u`, a finite Galois extension `L/F` in `Type u` and
  `o : relativeCohomology F L 2` with `2 • o = 0`, there are
  `E : IntermediateField F (SeparableClosure F)` with `Module.finrank F E = 2` and
  every infinite place of `E` complex, and a field `M : Type u` with
  `[Algebra E M] [FiniteDimensional E M] [IsGalois E M] [Algebra F M]
  [IsScalarTower F E M] [Algebra L M] [IsScalarTower F L M] [FiniteDimensional F M]
  [IsGalois F M]`, such that
  `relativeRestriction F E M 2 (relativeInflation F L M 2 o) = 0`: inflated to
  `Gal(M/F)` and restricted to `Gal(M/E)`, the class vanishes.

Auxiliary results:

- `intValuation_eq_of_sub_mem`: if `v(π) = exp (-1)` and `r - π ∈ v²` then
  `v(r) = exp (-1)`.
- `exists_valuation_eq_and_neg`: for a finite set `T` of finite places there is
  `a ∈ 𝓞 K` with `v(a) = exp (-1)` for every `v ∈ T` and `Re φ(a) < 0` for every
  real embedding `φ : K →+* ℂ`.
- `sq_ne_of_valuation_eq`: an element of a ring with `ν(c) = exp (-1)` for a
  `ℤᵐ⁰`-valued valuation `ν` is not a square.
- `finrank_adjoin_eq_two`: if `β² ∈ A` and `β ∉ A` then `[A(β) : A] = 2`.
- `two_dvd_localDegree_of_sq_eq`: if `E` contains `b` with `b² = a` and
  `v(a) = exp (-1)`, every local degree `localDegree E v w` above `v` is even.
- `isComplex_of_sq_eq`: if `a ∈ K` is negative at every real embedding of `K` and
  `E` contains a square root of `a`, every infinite place of `E` is complex.
- `relativeToContinuous_two_injective`: for a finite Galois extension `M/K` inside a
  Galois extension `S/K`, the Library's degree-two inflation
  `BrauerComparison.relativeToContinuous K M S 2` is injective.

## Proofs

`exists_valuation_eq_and_neg`: choose a uniformizer `π_v` at each `v ∈ T`
(`intValuation_exists_uniformizer`) and, by the Chinese remainder theorem
(`IsDedekindDomain.exists_forall_sub_mem_ideal`), `y` with `y - π_v ∈ v²`. Let `N`
be the product of the squares of the absolute norms of the primes of `T`, so that
`N ∈ v²` for `v ∈ T`, and `k = ⌈∑_φ |φ(y)|⌉ + 1`. Then `a = y - N k` still satisfies
`a - π_v ∈ v²`, hence `v(a) = exp (-1)` by `intValuation_eq_of_sub_mem`, and
`Re φ(a) ≤ |φ(y)| - N k < 0`.

`exists_quadratic_isComplex_brauerRestriction_eq_zero`: choose place embeddings
`ι`. By `brauerSequenceStatement` the set of finite places `v` with
`brauerLocalization ι v 2 x ≠ 0` is finite; add one finite place `v₀`
(`nonempty_heightOneSpectrum`) to get `T`. Take `a` from
`exists_valuation_eq_and_neg T`, a square root `b ∈ Ω` of `a`, and `E = K(b)`.
Since `v₀(a) = exp (-1)`, `a` is not a square in `K`, so `[E : K] = 2`
(`finrank_adjoin_eq_two`); `E` has no real place by `isComplex_of_sq_eq`. For
`v` with nonzero localization and `w | v`, the image `β` of `b` in `E_w` satisfies
`β² = a ∈ K_v` and `β ∉ K_v` (otherwise `a` would be a square in `K_v`, against
`Valued.v a = exp (-1)` from `valuedAdicCompletion_eq_valuation'`), so `K_v(β)` has
degree `2` over `K_v` and `2` divides `[E_w : K_v]` by the tower law
(`two_dvd_localDegree_of_sq_eq`, with the completion algebra of
`Langlands.Global.AdelicFunctoriality.FiniteExtension`). The theorem
`brauerRestriction_eq_zero_of_isComplex` with `m = 2` concludes.

`relativeToContinuous_two_injective`: the image `R` of `M` in `S` is a finite Galois
intermediate field with `M ≃ₐ[K] R`. By `relativeToContinuous_tower`,
`relativeToContinuous K M S 2 = relativeToContinuous K R S 2 ∘ relativeInflation K M R 2`;
the first map is injective by `relativeToContinuous_injective` and the second by
`finiteRelativeH2InflationExactness`.

`exists_quadratic_isComplex_relativeRestriction_eq_zero`: embed `L` in
`Ω = SeparableClosure F` and let `x` be the inflation of `o` to `Gal(Ω/F)` in the
cochain model, `unitsTowerMap F L Ω 2` after `isoGroupCohomology⁻¹`; then
`2 • x = 0`. The first theorem gives `E`. Let `M` be the compositum of `E` and the
image of `L`, viewed as an intermediate field of `Ω/E`
(`IntermediateField.extendScalars`); it is finite and Galois over `F` (a quadratic
extension is Galois, `IntermediateField.normal_sup`) and over `E`. Through
`unitsModuleContinuousEquiv_symm_relativeToContinuous` and
`relativeToContinuous_tower`, `x` is also the inflation of
`relativeInflation F L M 2 o`; by `unitsRestriction_unitsTowerMap` and
`unitsRestriction_isoGroupCohomology_inv`, `brauerRestriction E x` is the inflation
to `Gal(Ω/E)` of `relativeRestriction F E M 2 (relativeInflation F L M 2 o)`. This
inflation is zero, so the class is zero by `relativeToContinuous_two_injective`.

## Related Library results

`Langlands.Global.quadraticCompletionDegrees` (module
`Langlands.Global.Arithmetic.QuadraticCompletionDegrees`) gives, for a finite set of
finite places, a totally complex quadratic extension with even local degree above each of
them, as an abstract field extension of `F`. `Langlands.Brauer.numberFieldBrauerTwoTorsion`
(module `Langlands.Algebra.NumberFieldBrauerTwoTorsion`) uses it to split a central simple
algebra whose class is killed by two. The present module instead produces an intermediate
field of a chosen separable closure and works directly with the cohomological Brauer class
`H²(Gal(Ω/K), Ωˣ)` and with relative classes of finite Galois extensions.

## Source

The splitting of a class killed by two in `Br(K)` by a totally imaginary quadratic
extension is the step used in the proof of Proposition 6.16, item (2), of V. Platonov and
A. Rapinchuk, *Algebraic Groups and Number Theory* (Academic Press, 1994), printed
p. 335. The construction `K(√a)` with `a` of valuation one at the places of the
support and negative at the real places, and the local degree argument, are written
out here; the Lean route is internal to this Library.
