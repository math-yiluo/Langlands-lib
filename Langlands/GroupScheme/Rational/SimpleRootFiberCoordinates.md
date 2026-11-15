# Root field coordinates on both signs of a simple relative root fiber

Module `Langlands.GroupScheme.Rational.SimpleRootFiberCoordinates`, namespaces
`Langlands.GroupScheme` and `Langlands.GroupScheme.SimpleRootFiber`.

Worker 163, for Task 6836 (8c04a3ed-3fa6-4680-a59f-856738cb578b), SL2 half.

## Purpose

`AlgebraicSL2RootCoordinates` contains two records
`RootFieldCoordinatesOn i j s (±b) E` (module `QuasiSplitValuedRankOneCoordinates`). Each
consists of:

- an isomorphism `Multiplicative E ≃* U_{±b}(k)`;
- a rational character of `Z_E` restricting to the base change of `±b`;
- the torus conjugation formula.

The record's `rho_upper` and `rho_lower` fields require these isomorphisms to be
`t ↦ rho (upper t)` and `t ↦ rho (lower t)`.

This module builds both records for the data of `SimpleRootFiberPinning`: the pinning
`fiberPinning`, the fiber `O = fiberSet a` of a simple relative root `a` with `2 • a` not a
relative root, the field `E = fiberField` and the embeddings `τ = fiberEmbedding`. Here
`rho` is the descended `SplitPinning.fieldSL2` of `OrthogonalOrbitSpecialLinear`, and the
isomorphisms are `upperRootEquiv` and `lowerRootEquiv` of
`OrthogonalOrbitRootCoordinates`.

## Hypotheses

Both records keep the product hypotheses of `OrthogonalOrbitRootCoordinates` as explicit
arguments. They are not proved here:

- `hprodp`, `huniqp`: every point of the root group of `a_K` (for `S_K → G_K`) is an orbit
  product `orbitXp c` over `O`, with coordinates on `O` determined by the product;
- `hprodm`, `huniqm`: the same for `-a_K` with `orbitXm`.

They follow from the separately stated `SplitRelativeRootGroupProductStatement`, whose
proof is Task 7010. The field hypothesis `FamiliesFromField` of `OrthogonalOrbitRootCoordinates`
is discharged by `exists_eq_fiberEmbedding`.

## Contents

- `rationalCharacterEval_neg`: a negated rational character takes inverse values.
- `fiberEmbedding_eq_rootOrbitEmbeddingEquiv`: on the fiber, `fiberEmbedding t` is the
  Library's `rootOrbitEmbeddingEquiv` of the base root at the orbit element `rootOf t`.
- `fiberEmbedding_rootOrbitCharacter`: for a member `t` and `z ∈ T(k)`, the embedding `τ_t`
  sends the value at `z_E` of the root-orbit character `rootOrbitCharacter k K j β₀` to the
  value of the root of `t` at `z_K`. Proof: `rationalCharacterEval_rootOrbitCharacter`,
  `rootOrbitEmbeddingEquiv_characterValue` (module `RootOrbitCharacterAction`) and
  `rationalCharacterEval_baseChangedCharacter` (module `RootOrbitCharacterDescent`).
- `fiber_hg`: `f_K` followed by the pinning inclusion is the scalar extension of
  `groupHom f ≫ j`. `fiber_torusIso_inv`: the torus identification of the pinning is the
  identity on rational points.
- `positiveCoordinates : RootFieldCoordinatesOn (groupHom f ≫ j) j (groupHom f) a E`:
  - `equiv` is `upperRootEquiv`, applied to the fiber data and the hypotheses `hprodp`,
    `huniqp`;
  - `character` is `rootOrbitCharacter k K j β₀`;
  - `restriction` is `characterRestrict_rootOrbitCharacter`;
  - `conjugation` is `conj_fieldSL2_upper` with `χ z = rootOrbitCharacter(z_E)`; its
    hypothesis is `fiberEmbedding_rootOrbitCharacter`.
- `negativeCoordinates : RootFieldCoordinatesOn (groupHom f ≫ j) j (groupHom f) (-a) E`:
  - `equiv` is `lowerRootEquiv`;
  - `character` is `-rootOrbitCharacter k K j β₀`;
  - `restriction` follows from additivity of restriction and base change;
  - `conjugation` is `conj_fieldSL2_lower`, using `rationalCharacterEval_neg` and
    `map_inv₀`.
- `positiveCoordinates_equiv`, `negativeCoordinates_equiv`: the isomorphisms are
  `t ↦ fieldSL2 (upper t)` and `t ↦ fieldSL2 (lower t)`, by definition.

## Provenance

Internal glue between Task 6836 modules and the Library's root-orbit character API
(`RootOrbitCharacterDescent`, `RootOrbitCharacterAction`). It uses the same character as
the Library's `rootFieldCoordinatesOfOrbit` (module `RootFieldCoordinatesOfTorus`), with
the `SL₂` coordinates in place of that module's Lie-algebra coordinates. No source theorem
is cited. Every step is proved in Lean.
