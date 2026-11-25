# Multiplicative induced modules and Shapiro's lemma in Tate degrees 0 and −1

Module `Nyll.GaloisCohomology.Cyclic.Herbrand.Induced`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a subgroup `H` of a group `G` and a multiplicative `H`-module `B`, the induced module `InducedModule H` consists of the functions `f : G → B` with `f (h * x) = h • f x`, `G` acting by right translation; the model is imported from `ProCGroups.InducedFunctions`. For `G` finite cyclic with generator `σ`, the file proves the multiplicative Shapiro isomorphisms in Tate degrees 0 and −1 for the library's groups `HerbrandH0` and `HerbrandHMinusOne`.

## Main definitions and results

- `quotientMulEquivOfSplit`: a homomorphism `f : X →* Y` of commutative groups with a homomorphic section `s`, mapping `N` into `M` and `M` back into `N`, with kernel inside `N`, induces `X ⧸ N ≃* Y ⧸ M`; a general tool, also used outside this file.
- `inducedFixedEquiv H`: evaluation at `1` identifies the `G`-fixed points of `InducedModule H` with the `H`-fixed points of `B`, for any group `G`.
- `cyclicCosetEquiv H σ hgen : H × Fin [G:H] ≃ G`, `(h, i) ↦ h σ^i`; `subgroupGenerator H σ = σ^[G:H]`, which generates `H` (`zpowers_pow_index_eq`, `subgroupGenerator_generates`).
- `inducedCoordinates H σ hgen : InducedModule H ≃* (Fin [G:H] → B)`, `f ↦ (f (σ^i))ᵢ`, with the section `inducedSection` (first coordinate) and the product of coordinates `inducedCoordinateProduct`.
- `inducedEvaluation_tateNorm`: the value at `1` of `N_G f` is `N_H` of the product of the coordinates of `f`.
- `inducedHerbrandH0Equiv H σ hgen : HerbrandH0 G (InducedModule H) ≃* HerbrandH0 H B`.
- `inducedHerbrandHMinusOneEquiv H σ hgen : HerbrandHMinusOne G (InducedModule H) σ ≃* HerbrandHMinusOne H B (subgroupGenerator H σ)`.
- `inducedHerbrandH0EquivOfFiniteCyclic` and `inducedHerbrandHMinusOneEquivOfFiniteCyclic` (with `subgroupGeneratorOfGenerator`, `inducedCoordinatesOfFiniteCyclic`): the same for a group `G` without a `CommGroup` instance, commutativity being derived from `σ`.

## Proofs

In coordinates, `σ` acts as a cyclic shift whose wrap-around coordinate is acted on by `σ^[G:H]` (`inducedCoordinates_smul_generator`, `twistedFinRotate`), so the coordinate product sends `σ`-coboundaries to `σ^[G:H]`-coboundaries. A function whose coordinate product is `1` is a `σ`-coboundary, built from partial products (`finPartialProduct`). The coordinate product and the section then satisfy the hypotheses of `quotientMulEquivOfSplit`.

## Points to watch

- The induced module is the library's function model, not one of Mathlib's induced representations; note the left `H`-equivariance and the action by right translation.
- In degree −1 the subgroup side uses the specific generator `σ^[G:H]`.
- The main sections assume `CommGroup G` and `Fintype G`, with `hgen : ∀ x, x ∈ Subgroup.zpowers σ`. `Fintype H` is supplied by `Fintype.ofFinite`, and appears as a `let` in the statements of the `OfFiniteCyclic` versions.
- `inducedHerbrandH0Equiv` takes `σ` and `hgen` although `HerbrandH0` does not depend on `σ`; they fix the coordinates used in the construction.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Cyclic/Herbrand/Induced.lean`: the Lean file is the source byte for byte (SHA-256 `d17779a2331573c4573e65aa1de3c36af1c1fd4079b64c0ff8ad8449eb676d18`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
