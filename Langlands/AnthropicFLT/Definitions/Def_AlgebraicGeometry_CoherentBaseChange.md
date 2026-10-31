# Two-term complexes of finite free modules and their fibre cohomology

Module `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_CoherentBaseChange`, in namespace
`CoherentBaseChange`.

## Definitions

Let `R` be a commutative ring.

- A `TwoTermComplex R` is a linear map `d : C0 → C1` between finitely generated free `R`-modules
  `C0` and `C1`. It models a complex `0 → C0 → C1 → 0` that computes cohomology after base change.

For such a complex `G`:

- `G.fibreH0 𝔭`, for a prime `𝔭` of `R` with residue field `κ(𝔭)`, is the `κ(𝔭)`-dimension of the
  kernel of `d ⊗ κ(𝔭) : κ(𝔭) ⊗ C0 → κ(𝔭) ⊗ C1`, the fibre `H⁰` of the complex;
- `G.fibreH1 𝔭` is the `κ(𝔭)`-dimension of the cokernel of `d ⊗ κ(𝔭)`, the fibre `H¹`;
- `G.chi` is the Euler characteristic `rank C0 − rank C1`, an integer;
- `G.H0 A`, for an `R`-algebra `A`, is the kernel of the base change `d ⊗ A : A ⊗ C0 → A ⊗ C1`, as
  an `A`-submodule of `A ⊗ C0`;
- `G.kerBaseChangeHom A : A ⊗ ker d → G.H0 A` is the natural `A`-linear map induced by the inclusion
  `ker d → C0`.

`kerBaseChangeHom_apply_coe` records the value of `kerBaseChangeHom` in `A ⊗ C0` (proved by `rfl`).

## Provenance and licence

This file is a port of `Definitions/Def_AlgebraicGeometry_CoherentBaseChange.lean` from the
Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md`
are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice
applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`.

The file imports only Mathlib, so its imports are unchanged.
