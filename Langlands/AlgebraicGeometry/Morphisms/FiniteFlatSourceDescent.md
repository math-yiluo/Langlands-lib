# Local finite type descends along finite flat surjections of the source

`Langlands.AlgebraicGeometry.Morphisms.FiniteFlatSourceDescent`.

## Source and licence

Adapted from `P2M/Sol/S_AlgebraicGeometry_LocallyOfFiniteType_of_comp_of_isFinite_of_flat_of_surjective.lean`
(SHA-256 `18a0158a578e29c0443851664c69928d81b0cedcf55c59a4f446d726b4ce86a9`) of the Anthropic
Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`;
registered literature `anthropic-flt-complete-lean-source-6e837e75`, project literature folder
"Anthropic - Fermat's Last Theorem - complete Lean source at
6e837e75355538c7f80bab5b956861e86c4eacc2"). FLT states the result in
`Theorems/Thm_AlgebraicGeometry_LocallyOfFiniteType_of_comp_of_isFinite_of_flat_of_surjective.lean`
(SHA-256 `5f98031b65fab2bc6e089562b3526caa0d2eda9d29e38c463c5a2243f3b04dc2`) as
`AlgebraicGeometry.LocallyOfFiniteType.of_comp_of_isFinite_of_flat_of_surjective`.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT
`LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. The FLT
`ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- The FLT theorem `solution` is moved from the wrapper namespace `P2MW.<file>` to
  `Langlands.AlgebraicGeometry.FiniteFlatSourceDescent` and renamed
  `locallyOfFiniteType_of_comp_of_isFinite_of_flat_of_surjective`.
- `P2M.Util` is not imported; the FLT lakefile option
  `backward.isDefEq.respectTransparency.types false` is set before the theorem.
- An attribution header and a module docstring are added. The statement and proof are
  otherwise the FLT text.

## Declaration

`locallyOfFiniteType_of_comp_of_isFinite_of_flat_of_surjective`: let `f : X ⟶ Y` be finite,
flat and surjective, let `g : Y ⟶ Z` be such that `f ≫ g` is locally of finite type, and let
`Z` be locally Noetherian. Then `g` is locally of finite type.

Proof: by the affine-local characterization (`HasRingHomProperty.iff_appLE`), take affine
opens `U ⊆ Z` and `V ⊆ g⁻¹U`, and the affine open `V' = f⁻¹V`. The ring map
`Γ(Y, V) → Γ(X, V')` is finite (finiteness of `f` on affine opens). It is flat, and `Spec` of it
is surjective because `f` is surjective, so it is injective. `Γ(Z, U) → Γ(X, V')` is of finite
type and `Γ(Z, U)` is Noetherian. The Artin–Tate lemma `fg_of_fg_of_fg` then shows that
`Γ(Y, V)` is a finitely generated `Γ(Z, U)`-algebra.
