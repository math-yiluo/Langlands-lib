# Local-global compatibility at a ramified real place

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ComplexificationArtin.InfinitePlaceCompatibility`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite abelian extension `L/K` of number fields and a real place `v` of `K` that ramifies in `L`, the file proves that the global norm-residue symbol of the idele class with `-1` at `v` (and `1` elsewhere) is the library's chosen local Artin symbol of `-1` at `v`, which acts as complex conjugation for the chosen place above `v`. The proof passes through an auxiliary quadratic extension, the "complexification overfield" `L(i)`, over the fixed field `K'` of a complex conjugation of `L(i)`.

## Main results

- `globalNormResidueMonoidHom_infinitePlaceIdeleClass_neg_one_of_ramified`: under the hypothesis `hRamified` that the chosen place of `L` above `v` is ramified over `K`, `globalNormResidueMonoidHom K L` sends the one-place class of `-1` at `v` to `chosenInfinitePlaceArtinMonoidHom v (-1)`.
- `ramifiedInfinitePlaceRealFixedPlace v hRamified`: the place of `K'` below the complex place of `L(i)`; it is real (`ramifiedInfinitePlaceRealFixedPlace_isReal`), lies over `v`, and is ramified in `L(i)`.
- `ramifiedInfinitePlaceOverextension_localArtin_neg_one` and `ramifiedInfinitePlaceOverextension_globalNormResidue_neg_one`: for `L(i)/K'`, both the local Artin symbol and the global norm-residue symbol of `-1` at this place are the distinguished complex conjugation.
- `ramifiedInfinitePlaceOverextension_globalNormResidueOfEmbedding_neg_one`: the same holds for the norm-residue map built from any embedding `j : L(i) → SeparableClosure ℚ`, since the Galois group has two elements and all these maps have the norm range as kernel.
- `ramifiedInfinitePlaceOverextensionRestriction_conjugation`: restricting that conjugation from `L(i)` to `L` gives the local Artin symbol of `-1` at `v`.
- `infinitePlaceComplexificationOverfieldSeparableClosureEmbedding`: an embedding of `L(i)` extending the standard embedding of `L`, chosen by `Classical.choose`.

## Proof

The main theorem is a diamond. Upstairs, the value for `L(i)/K'` is complex conjugation, from the overextension computation that the docstring describes as the rational fourth-root product formula. The norm from `K'` to `K` of the `-1` class at the real place is the `-1` class at `v` (`ideleClassNorm_infinitePlaceIdeleClass_neg_one_of_isReal`). Norm-restriction naturality for embedded norm-residue maps (`globalNormResidueMonoidHomOfEmbedding_norm_restriction`) and the comparison of the embedded map with the standard one at the standard embedding then give the equality.

## Caveats

- Only the element `-1` at a ramified real place is treated; the hypothesis concerns the place chosen by `chosenInfinitePlaceAbove`.
- `chosenInfinitePlaceArtinMonoidHom` and `globalNormResidueMonoidHom` are the library's own maps.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/ComplexificationArtin/InfinitePlaceCompatibility.lean`: the Lean file is the source byte for byte (SHA-256 `c62c3b34751d2e29e728b9a3e1cd3d1e0fcd4a1bd27f1ac30ff3316e072c241b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
