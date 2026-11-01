# The ideal sheaf of admissible functions

Author: Worker 716. This is an internal helper module for
`Langlands.AlgebraicGeometry.Modules.coherentIntegralIdealFiltration`. The ideal sheaf
is a derived construction for the proof.

## Admissible functions

For an open `V` of the closed subscheme `Z = w.Z` and `a ∈ Γ(Z, V)`, `w.Mem V a` means that
`InT W (a|_{i⁻¹ W})` holds for every open `W` of `X` with `i⁻¹ W ≤ V`. Every open of `Z` is
a preimage, but not of a unique open of `X`. Quantifying over all `W` makes the predicate
independent of choices.

- `InT.mul`: admissibility is stable under multiplication by any `c ∈ Γ(Z, i⁻¹ W)`. Locally
  on affine opens of `X`, `c` lifts to `X` (`app_surjective`); then use `InT.smul` and glue
  with `inT_of_local`.
- `mem_res`: admissibility is stable under restriction.
- `mem_iff_inT`: on `V = i⁻¹ W`, `Mem` is `InT W` (`inT_iff_forall`).
- `mem_of_local`: admissibility is local on `Z`. Let `W` have `i⁻¹ W ≤ V`. A point of `W`
  in `Zc` is `i z`, and `z` has a neighbourhood `V'` on which `a` is admissible. Since `i`
  is an embedding, `V' = i⁻¹ O` for an open `O`, and then `W ⊓ O` works. A point outside
  `Zc` is handled on `W ⊓ Zcᶜ` by `inT_of_disjoint`. Then apply `inT_of_local`.

## The sheaf

`w.idealSub : SheafOfModules.Submodule (structureModule w.Z)` has, over `V`, the
admissible functions as a submodule of `Γ(Z, V)` (Mathlib's `SheafOfModules.Submodule`).

- The submodule axioms come from `InT.add`, `inT_zero` and `InT.mul`; the action of
  `Γ(Z, V)` on the structure sheaf is multiplication.
- Stability under restriction is `mem_res`.
- The sheaf condition, membership local for covering sieves, is `mem_of_local`.

`w.I` is the associated module `idealSub.toSheafOfModules` on `Z`, and `w.ι` its inclusion
into `structureModule w.Z`; `w.ι` is a monomorphism.
