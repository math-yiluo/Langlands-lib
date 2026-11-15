# `H₁(L_{κ/A})` is the cotangent space `𝔪/𝔪²`

For a local ring `(A, 𝔪, κ)`, the identification `H₁(L_{κ/A}) = 𝔪/𝔪²` is used throughout Stacks,
More on Algebra, Proposition 15.36.1 (07E5); see the proof of (3) ⇔ (4) there. This module proves
the dimension version needed to compare embedding dimensions. All declarations live in
`Langlands.CommutativeAlgebra.Popescu.Faltings`. `CotangentSpace A` is Mathlib's
`IsLocalRing.CotangentSpace A = 𝔪/𝔪²`.

## `residueExt` and its basic facts

- `residueExt A`: the `Algebra.Extension A κ` with underlying ring `A` itself, the residue map, and
  a chosen section.
- `residueExt_ker`: its kernel is `𝔪`.
- `residueExt_ker_le`: the kernel is contained in `𝔪` (the comap of `𝔪` along the identity), the
  form needed by `Ideal.mapCotangent` below.
- `residueExt_h1Cotangentι_surjective`: every element of its conormal module lies in `H₁`. The
  cotangent complex lands in `κ ⊗ Ω_{A/A} = 0`.
- `residueExt_map_defaultHom_bijective`: `H₁(L_{κ/A})`, computed with the canonical presentation,
  maps bijectively to `H₁` of `residueExt`. This is Mathlib's `Extension.H1Cotangent.equiv`, which
  says that `H₁` does not depend on the presentation.

## `residueExtCotangentMap`, `residueExtCotangentMap_apply`, `residueExtCotangentMap_bijective`

`residueExtCotangentMap` is the `κ`-linear map from the conormal module `ker/ker²` of `residueExt`
to `𝔪/𝔪²`, induced by the identity of `A` (`Ideal.mapCotangent`). It is `κ`-linear because `κ`
acts on both sides through any lift to `A`. It is bijective:
- injective, because `ker = 𝔪`, so `x ∈ ker²` iff `x ∈ 𝔪²`;
- surjective, because every class in `𝔪/𝔪²` comes from an element of `ker = 𝔪`.

## `rank_h1Cotangent_residueField`, `rank_h1Cotangent_residueField_eq_finrank`

- `rank_h1Cotangent_residueField`: `dim_κ H₁(L_{κ/A}) = dim_κ 𝔪/𝔪²`, by composing the three
  linear equivalences above.
- `rank_h1Cotangent_residueField_eq_finrank`: if `A` is Noetherian, this rank is the finite
  `Module.finrank κ (CotangentSpace A)`.
