# Norm maps compatible with unit filtrations

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.NormFiltration`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file studies an abstract norm map between two filtered groups. The data are groups `G` and `H` with the library's integer-valued valuations, a `ValuedNorm` `N` from `H` to `G` (with underlying homomorphism `N.toHom : H →* G`), decreasing subgroup filtrations `UH^n` of `H` and `UG^n` of `G` (`AntitoneSubgroupFiltration`), and a level function `t : ℕ → ℕ`. If `N` sends each `UH^n` into `UG^(t n)`, it induces maps on levels, quotients, subquotients and graded pieces. The file gives kernel, injectivity and surjectivity criteria for these maps.

## Definitions

- `MapsFiltrationLevels N UG UH t`: the proposition that `N(UH^n) ⊆ UG^(t n)` for every `n`. `mapsFiltrationLevels_of_le` weakens it to any smaller level function.
- `mapLevelOfMapsFiltrationLevels`: the restriction `UH^n → UG^(t n)`.
- `quotientMapOfMapsFiltrationLevels`: the induced map `H / UH^n → G / UG^(t n)`.
- `filtrationPreimageSubgroup` and `filtrationPreimageClassInQuotient`: the preimage `N⁻¹(UG^(t n))` and its image in `H / UH^n`.
- `principalUnitSubquotientMapOfMapsFiltrationLevels`: for `m ≤ n` and `t m ≤ t n`, the map `UH^m / UH^n → UG^(t m) / UG^(t n)`. `principalUnitGradedPieceMapOfMapsFiltrationLevels` is its graded-piece case `UH^n / UH^(n+1) → UG^(t n) / UG^(t (n+1))`.

## Results

- `quotientMapOfMapsFiltrationLevels_ker_eq_filtrationPreimageClass`: the kernel of the quotient map is the class of `N⁻¹(UG^(t n))`. Consequently the map is injective if and only if every `x` with `N x ∈ UG^(t n)` lies in `UH^n` (`quotientMapOfMapsFiltrationLevels_injective_iff_forall_norm_mem`).
- First isomorphism theorems: `quotientModuloFiltrationPreimageClassEquivRange` identifies `H / UH^n` modulo this kernel with the range, and `quotientModuloFiltrationPreimageClassEquivTargetOfSurjective` with `G / UG^(t n)` when the quotient map is surjective.
- `quotientMapOfMapsFiltrationLevels_surjective_iff_exists_div_mem`: the quotient map is surjective if and only if every element of `G` is a norm modulo `UG^(t n)`. It is surjective whenever `N.toHom` is (`quotientMapOfMapsFiltrationLevels_surjective_of_surjective`).
- Naturality: the quotient maps commute with changing the source level or coarsening the target level, and surjectivity passes to the coarser quotients.
- For the subquotient and graded-piece maps: criteria on representatives for being trivial, for equality and for surjectivity (every `y` in `UG^(t m)` is a norm from `UH^m` modulo `UG^(t n)`), and compatibility with the ambient quotient map.

Most criteria come in several equivalent forms (`x / y` or `y⁻¹ * x`; surjectivity or `range = ⊤`).

## Watch for

- Everything is abstract group theory. No norm of a field extension appears, and the compatibility `MapsFiltrationLevels` is a hypothesis of every induced map; the file does not prove it for any concrete norm map.
- The groups need not be commutative: normality of the relevant filtration subgroups is assumed as instance arguments.
- The level function `t` is not assumed monotone; the subquotient maps take `t m ≤ t n` as an explicit hypothesis.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/NormFiltration.lean`: the Lean file is the source byte for byte (SHA-256 `95c770065b18a2c237675c5a3f6120ee6cbd42d4d2e844493c4b2a92483f1e17`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
