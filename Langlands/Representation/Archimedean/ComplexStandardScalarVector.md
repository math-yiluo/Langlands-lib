# A scalar vector in every complex standard module

Module `Langlands.Representation.Archimedean.ComplexStandardScalarVector`, namespace
`Langlands.Archimedean.ComplexStandardScalarVector`. It is a
step in the proof of `ComplexPlaceParameterIrreducibleStatement`. Provenance: internal.

Notation: `X(ds)` (`KF n ds`) is the space of `U(n)`-finite functions of the complex standard
module of a list `ds` of complex characters, `kFiniteFunctions (complexStandardModule n ds)
(unitaryCompact ℂ n)`, with `U(n)` acting by `complexStandardRep n ds` (right translation).

## Definition

- `IsScalarVector ds f₀`: `f₀ ∈ X(ds)` is nonzero, and every `ℂ`-linear endomorphism `E` of
  `X(ds)` that commutes with `complexStandardRep n ds k` for all `k ∈ U(n)` satisfies
  `E f₀ = a • f₀` for some `a ∈ ℂ`.

Such a vector spans a `U(n)`-type that occurs with multiplicity one. The name is internal.

## Results

- `exists_isScalarVector_of_sorted`: if `ds` has length `n` and nondecreasing weights
  (`ds.Pairwise (·.weight ≤ ·.weight)`), then `X(ds)` has a scalar vector. The construction
  follows steps 1, 2, 4 and 5 of the Library proof `irreducible_of_sorted` (module
  `ComplexTemperedStandardIrreducibleProof`), without the cyclicity part:
  1. `exists_minorWeight_eq` writes the weights as the minor weights of some `c : Fin n → ℕ`
     and `d : ℤ`. Then `positionCharacter_untwist` writes each position character of `ds` as
     `z^{l_i}` times the position character of the weight-zero list `untwist ds`.
  2. `ComplexSphericalLieGroup.exists_spherical` gives a `U(n)`-fixed `T` in `X(untwist ds)`
     with `T(1) = 1`, so `T = 1` on `U(n)`.
  3. `ComplexMinorProduct.mulV c d _ T ∈ X(ds)` is the function
     `g ↦ minorMonomial c d (g) · T(g)`. On `U(n)` it equals the minor monomial
     (`mulV_coe`).
  4. It is nonzero, since the minor monomial does not vanish at `revUnitary n`
     (`minorMonomial_revUnitary_ne_zero`). It is a scalar vector by the Library theorem
     `complexLowestKTypeMultOne`.
- `IsScalarVector.of_equiv`: a bijective `U(n)`-equivariant linear map `Φ : X(ds) ≃ X(es)`
  carries scalar vectors of `X(es)` back to scalar vectors of `X(ds)`. For an equivariant
  endomorphism `E` of `X(ds)`, apply the hypothesis to `Φ ∘ E ∘ Φ⁻¹`.
- `exists_isScalarVector`: **every `X(ds)` with `ds` of length `n` has a scalar vector.**
  - Write `ds = List.ofFn d` (Library `ComplexPermutation.ofFn_get_eq`), and let `τ` be
    `Tuple.sort` of the weights `j ↦ (d j).weight` (Mathlib). Then `e = d ∘ τ` has
    nondecreasing weights (`Tuple.monotone_sort`, `List.pairwise_ofFn`).
  - The Library maps `ComplexPermutation.permKMap d τ⁻¹ : X(ds) → X(List.ofFn e)` and
    `permKMap e τ : X(List.ofFn e) → X(ds)` are injective and `U(n)`-equivariant. The lists
    are identified by rewriting.
  - By `ComplexPermutation.surjective_of_injective_of_kMap` the first map is also surjective,
    hence a bijective equivariant map.
  - Apply `exists_isScalarVector_of_sorted` to `List.ofFn e`, then `IsScalarVector.of_equiv`.

All results use only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

Internal infrastructure. It records, for every complex standard module, the lowest
`U(n)`-type multiplicity-one vector of the Library's Duflo-style argument (module
`ComplexLowestKTypeMultOne`). Here the vector is used in the irreducibility proof of
`Langlands.Global.RankinSelberg.ComplexPlaceParameterIrreducibleProof`.
