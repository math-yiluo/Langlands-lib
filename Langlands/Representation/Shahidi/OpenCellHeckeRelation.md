# The minuscule Hecke relations of the unramified two-block section

Module `Langlands.Representation.Shahidi.OpenCellHeckeRelation`, namespace
`Langlands.Shahidi.OpenCell`.

## Contents

- `residuePowUnit K z = q^z` as a unit; `sectionParameter K a c s =
  (a q^(-s(t+1)/N), c q^(s(r+1)/N))`, the Satake parameter of the section (`N = r + t + 2`).
- `heckeScalar_eq`: for `q > 0`, `k₁ ≤ r + 1` and `k₂ ≤ t + 1`, the scalar identity combining
  the block Hecke eigenvalues and the modulus.
- `determinantNorm_unipotent_mul`, `twoBlockModulus_torus`, `sum_subsetExponent`: auxiliary
  identities for the modulus at torus points.
- `isLeviEquivariant_fullΦ`: for `ψ` of conductor `𝒪`, the section's Levi function is
  equivariant for the standard characters of the two blocks.
- `sum_sphericalWhittaker_torus_subsetExponent`, `fullΦ_torus_add`, `sum_fullΦ_torus_split`:
  the Library's Hecke relation of `sphericalWhittaker` at a dominant torus point in subset form,
  and its two-block combination.
- `sum_liftFunction_fullΦ_torus`: let `ψ` have conductor `𝒪` and let `σ : Λ → 𝒪` be a system of
  representatives of the residue field (`|Λ| = q`, injective and surjective modulo the maximal
  ideal). At a torus point `ϖ^ν` with `ν` antitone on each block,
  `∑_α F(ϖ^ν · labelledRep α) = q^(k(N-k)/2) e_k(χ) F(ϖ^ν)`, the sum over the labelled minuscule
  coset representatives of size `k` and `χ = sectionParameter K a c s`. The proof splits subsets
  along the blocks (`Langlands.Representation.Shahidi.OpenCellHeckeSplit`), uses
  `sum_liftFunction_torus_mul_labelledRep` and the Library's Hecke relations of
  `sphericalWhittaker` on each block.

## Provenance

Derived from the Hecke eigen-equations of the spherical Whittaker functions on the Levi blocks
(Library, `Conductor.UnramifiedSphericalWhittaker`, `Unramified.PrincipalSeriesHecke`).
