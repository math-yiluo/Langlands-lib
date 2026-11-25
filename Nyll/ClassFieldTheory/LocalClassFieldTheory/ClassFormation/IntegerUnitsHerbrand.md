# The Herbrand quotient of the integer units

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.IntegerUnitsHerbrand`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K` be a nonarchimedean local field and `L/K` a finite Galois extension with a valuative relation extending that of `K`, `𝒪_L` being the integral closure of `𝒪_K` in `L`. For a subgroup `V` of `𝒪_Lˣ` equal as a set to `chosenNormalBasisPrincipalUnitSet K L n` (the normal-basis neighbourhood `1 + π_Kⁿ M`), the file studies the sequence `1 → V → 𝒪_Lˣ → 𝒪_Lˣ/V → 1` with its Galois actions and computes the Herbrand quotient `h(G, 𝒪_Lˣ) = 1` for cyclic `G = Gal(L/K)`.

## Main results

- `chosenNormalBasisIntegerUnitsHerbrand_shortExact`: the inclusion of `V` and the quotient map are `Gal(L/K)`-equivariant, the inclusion is injective, the quotient map is surjective, and its kernel is the image of `V`.
- `integerUnits_herbrandQuotient_eq_one_of_chosenNormalBasis`: given a generator `g` of `Gal(L/K)`, finiteness of `𝒪_Lˣ/V`, and the hypotheses that `HerbrandH0 G V` and `HerbrandHMinusOne G V g` are subsingletons, the Herbrand quotient of `𝒪_Lˣ` is defined and equals 1.
- `exists_integerUnits_herbrandQuotient_eq_one_of_large_chosenNormalBasisLevel`: assuming in addition that `L` is a nonarchimedean local field and `𝒪_L` is a finite `𝒪_K`-module, there is `c` such that for every `n ≥ c` the same conclusion holds; finiteness of the quotient now comes from `exists_finite_chosenNormalBasisIntegerUnitsQuotient`.

## Proof

The Herbrand quotient of `V` is 1 because both groups are trivial, that of the finite quotient is 1, the middle term's quotient is defined by `herbrandQuotientDefined_middle_of_left_right`, and `herbrandQuotient_multiplicative_of_shortExact` gives `h(𝒪_Lˣ) = h(V) · h(𝒪_Lˣ/V) = 1`.

## Points to note

- The vanishing of `H⁰(G, V)` and `H⁻¹(G, V)` is a hypothesis of both theorems; it is not proved in this file. The last theorem only removes the finiteness hypothesis.
- `HerbrandH0` and `HerbrandHMinusOne` are the library's own multiplicative Herbrand groups for a `MulDistribMulAction`; the degree −1 group and the quotient depend on the chosen generator `g`.
- The Galois actions on `V` and on the quotient are local instances that depend on the equation `hV`.
- The fields `K` and `L` are taken in `Type` (universe 0).

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/IntegerUnitsHerbrand.lean`: the Lean file is the source byte for byte (SHA-256 `eb88158fd29868d70e94f149f11d3bdc125633193e235483c87a963af21587ef`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
