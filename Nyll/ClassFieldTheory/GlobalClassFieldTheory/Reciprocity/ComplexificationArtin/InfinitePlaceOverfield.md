# The field L(i) at an infinite place

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ComplexificationArtin.InfinitePlaceOverfield`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite abelian extension `L/K` of number fields and an infinite place `v` of `K`, the file builds the concrete field `L(i)` inside `ℂ`: the compositum of the image of `L` under the complex embedding of the chosen place of `L` above `v` with the field of fourth roots of unity. It shows that `L(i)` is a totally complex number field, abelian over `K`, and, when the place above `v` is ramified, stable under complex conjugation.

## Main definitions and results

- `complexEmbeddingFieldRange_map_complexConjugation`: if `φ : L → ℂ` and `σ ∈ Aut(L/K)` satisfy `IsConj φ σ` (complex conjugation after `φ` is `φ ∘ σ`), then `φ(L)` is stable under complex conjugation.
- `infinitePlaceComplexificationOverfield v`: `L(i)`, an intermediate field of `ℂ/ℚ`, defined from the embedding of `chosenInfinitePlaceAbove v` and `complexFourthRootField`. Instances make it a number field and an `L`-algebra and `K`-algebra through `infinitePlaceComplexificationOverfieldEmbedding`, with the evident scalar towers, finite over `L`.
- `infinitePlaceEmbeddedExtensionField v` (the copy of `L`) and `infinitePlaceBaseFourthRootField v` (`K` with the fourth roots of unity adjoined, a cyclotomic extension for `{4}`) are abelian over `K`; `infinitePlaceComplexificationFactors_sup` says they generate `L(i)`. Hence the instance `infinitePlaceComplexificationOverfield_isAbelianGalois_over_base`: `L(i)/K` is abelian Galois. It is also totally complex.
- `infinitePlaceComplexificationOverfieldComplexPlace v`: the complex place of `L(i)` given by its inclusion in `ℂ`.
- `infinitePlaceComplexificationOverfield_map_complexConjugation`: under the hypothesis `hRamified` that the chosen place above `v` is ramified over `K`, complex conjugation maps `L(i)` onto itself.
- `ramifiedInfinitePlaceOverfieldConjugation v hRamified`: the resulting automorphism of `L(i)`; it acts as complex conjugation and squares to the identity.

## Proof

Stability of the `L`-factor uses that the library's local Artin symbol of `-1` at the ramified place is a conjugation for the chosen embedding (`chosenInfinitePlaceArtinMonoidHom_neg_one_isConj_of_ramified`); the fourth-root factor is stable on its own. That `L(i)/K` is abelian comes from the compositum of two abelian extensions.

## Caveats

- `L(i)` depends on the place chosen by `chosenInfinitePlaceAbove`, through its complex embedding.
- Conjugation stability is proved only under `hRamified`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/ComplexificationArtin/InfinitePlaceOverfield.lean`: the Lean file is the source byte for byte (SHA-256 `c767d933506350c069d9bc7e2db8445a1db827451018dc737f705d01febb323e`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
