# Algebraic structure of the localized completion

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Algebra`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a field extension, `v` an absolute value on `K` with completion `K_v`, and `w` an extension of `v` to `L`. Write `L_w` for the algebraic localization `LocalizedCompletion v w`. This file gives named algebra structures on it and the basic facts about `L_w` over `K_v` used by the localized class-formation files.

## Structures

- `localizedCompletionBaseAlgebra`: the `K_v`-algebra structure on `L_w`.
- `localizedCompletionGlobalAlgebra`, `localizedCompletionIsScalarTower`: the `K`-algebra structure through `K → K_v → L_w`, and the scalar tower.
- `localizedCompletionToAlgHom`: the canonical embedding `L → L_w` as a `K`-algebra homomorphism.

## Results

- `localizedCompletionFiniteDimensional`: `L_w` is finite-dimensional over `K_v` when `L/K` is finite and `v` is nontrivial.
- `localizedCompletionIsGalois`: `L_w/K_v` is Galois when `L/K` is.
- `localizedCompletion_adjoin_range_eq_top`: `L_w` is generated over `K_v` by the image of `L`.
- `localizedCompletion_adjoin_image_eq_top_of_adjoin_eq_top`: the image of a primitive element of `L/K` is a primitive element of `L_w/K_v`.
- `localizedCompletion_generator_isSeparable`, `localizedCompletion_generator_minpoly_splits`: for `L/K` Galois, the image of every element of `L` is separable over `K_v`, and its minimal polynomial over `K_v` splits in `L_w`.
- `localizedCompletion_isAbelianGalois`: if `L/K` is abelian and `v` nontrivial, then `L_w/K_v` is abelian.
- `localizedCompletion_baseField_comap_eq_fixedField_decompositionGroup`: for `L/K` Galois and `v` nontrivial, the elements of `L` whose images lie in `K_v` form the fixed field of the decomposition group of `w`.

## Proofs

Most statements repackage results on algebraic localizations from the ramification part of the library (`algebraicLocalization_isGalois`, `decompositionField_localization_adjoin_range_eq_top` and the separability and splitting lemmas). The primitive-element statement follows from the generation result. The last two use the isomorphism `decompositionGroupEquivAlgebraicLocalizationAut` between the decomposition group and `Aut(L_w/K_v)`: commutativity is transported along it, and the fixed-field statement combines it with the Galois characterization of `K_v` inside `L_w`.

## Points to note

The two algebra structures are reducible definitions and the statements carry them as `let`-bound instances; nothing here is a global instance. `LocalizedCompletion` is the library's algebraic model of the completion, not the metric completion itself.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/LocalizedCompletionCohomology/Algebra.lean`: the Lean file is the source byte for byte (SHA-256 `9001ce9a46c099ac19c77723f2663b382eed2087d620b3fd8dc86203550a4f01`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
