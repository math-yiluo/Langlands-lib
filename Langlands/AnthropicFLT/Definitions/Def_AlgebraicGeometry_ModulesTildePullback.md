# Pullback of quasi-coherent sheaves along a morphism of affine schemes

Module `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesTildePullback`, in namespace
`AlgebraicGeometry`. Rings live in a fixed universe `u`; `φ : R ⟶ S` is a map of commutative rings.

## Definitions and results

- `Scheme.Modules.pushforwardSpecCompΓIso φ`: for a sheaf of modules `N` on `Spec S`, the global sections
  of its pushforward along `Spec S ⟶ Spec R`, as an `R`-module, are the global sections of `N` with
  scalars restricted along `φ`. This is a natural isomorphism of functors to `R`-modules, given on each
  object by the identity of the underlying groups.
- `tilde.functorCompPullbackSpecIso φ`: the natural isomorphism `(Spec φ)^* ∘ ~ ≅ ~ ∘ (S ⊗_R –)`
  between functors from `R`-modules to sheaves of modules on `Spec S`. For an `R`-module `M`, the
  pullback of `M~` is `(S ⊗_R M)~`. It is obtained by uniqueness of left adjoints, since both functors
  are left adjoint to the same functor (`Γ` after pushforward, compared by the previous isomorphism).
- `tilde.pullbackSpecIso φ M : (Spec φ)^* (M~) ≅ (S ⊗_R M)~` is its component at `M`
  (`tilde.functorCompPullbackSpecIso_app`), and `tilde.pullbackSpecIso_hom_naturality` its naturality
  in `M`.

## Provenance and licence

This file is a port of `Definitions/Def_AlgebraicGeometry_ModulesTildePullback.lean` from the Anthropic
Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
(registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026
Anthropic, PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE`
and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no
third-party notice applies. Declaration names and namespaces are FLT's. The port makes only these
changes:

- an attribution header is added above the imports;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`.

The file imports only Mathlib, so its imports are unchanged.
