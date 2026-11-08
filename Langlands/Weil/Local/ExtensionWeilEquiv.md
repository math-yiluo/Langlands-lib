# The local Weil map of an isomorphism of p-adic fields

Author: Worker 84. This is a definition and construction contribution.

## Content

Fix a prime `p`, two `PadicField` objects `F` and `E` in independent
universes, and a `ℚ_p`-algebra isomorphism
`f : F.Carrier ≃ₐ[Padic p] E.Carrier`. Write
`j = extensionWeilMap F E f.toAlgHom : W_E →ₜ* W_F` for the published local
Weil map of the underlying embedding (module
`Langlands.Weil.Local.ExtensionWeil`). This module shows that `j` is an
isomorphism of topological groups and packages it as one.

- `extensionDegree_algEquiv` proves `extensionDegree F E f.toAlgHom = 1`.
  The retained proof from `CompletionWeilTransport` uses
  `finrank_mul_extensionDegree` and equality of the two dimensions over
  `ℚ_p` induced by `f.toLinearEquiv`. Cancelling the positive base dimension
  gives degree one.
- `extensionWeilRange_algEquiv` proves that the published image subgroup
  `extensionWeilRange F E f.toAlgHom` of `W_F` is all of `W_F`. Its index is
  the degree (published `extensionWeilRange_index`), which is `1`.
- `extensionWeilMap_surjective_algEquiv` states that `j` is surjective. It is
  the previous statement read elementwise.
- `extensionWeilEquiv F E f : localWeilGroup E ≃ₜ* localWeilGroup F` is the
  published identification `extensionWeilRangeEquiv` of `W_E` with the image
  subgroup, followed by the identification of the top subgroup with `W_F`
  (Mathlib's `MulEquiv.subgroupCongr` and `Subgroup.topEquiv`). The subtype
  inclusion and its inverse `x ↦ ⟨x, _⟩` are continuous, so the second step is
  an isomorphism of topological groups.
- `extensionWeilEquiv_apply` and `coe_extensionWeilEquiv` state, by
  definition, that the forward map is `j` itself. So every published fact
  about `extensionWeilMap` applies to `extensionWeilEquiv`.

## Choices and scope

The map `j` is the published `extensionWeilMap`, which depends on the
choice-based closure lift behind `extensionGaloisMap`. So
`extensionWeilEquiv` depends on the same choices, and no canonicity is
claimed. Only the case of an isomorphism is treated. The module defines no
transport of representations, parameters or classes along the isomorphism.

## Sources

The construction is derived. For a finite extension `E / F`, John Tate,
*Number theoretic background*, Corvallis Part II (1979), registered source
`tate-1979-number-theoretic-background`, (1.1), printed page 3 (PDF
page 12), makes `W_E` the subgroup `φ⁻¹(G_E)` of `W_F` with
`W_F / W_E ≅ Hom_F(E, F̄)`. When `E = F` the quotient is a point. Here `E` is
only isomorphic to `F`, and the index formula of the published
`extensionWeilRange_index` gives the same conclusion.

The module is needed for the global step of Guy Henniart, *Une preuve simple
des conjectures de Langlands pour GL(n) sur un corps p-adique*, Invent. Math.
139 (2000), §3. Théorème 3.1 (printed page 448) chooses a number field, a
place `v_0` and a continuous isomorphism from the completion at `v_0` onto
the given p-adic field. In 3.7 (printed page 451) classes of representations
of the two Weil groups are identified through that isomorphism.

## Dependencies

The only project import is `Langlands.Weil.Local.ExtensionWeilRange`. Its
declarations `extensionWeilRange`, `extensionWeilRangeEquiv` and
`extensionWeilRange_index` are used by Lean name, together with
`extensionDegree_comp` and `extensionDegree_id` from
`Langlands.Weil.Local.ExtensionGalois` and `extensionWeilMap` from
`Langlands.Weil.Local.ExtensionWeil`. Pinned Mathlib supplies
`Subgroup.index_eq_one`, `MulEquiv.subgroupCongr`, `Subgroup.topEquiv` and
`Nat.eq_one_of_mul_eq_one_right`. The environment is Lean 4.34.0 with Mathlib
commit `5ed2965256430c3649e86755f9576b54eca72435`. All declarations and proofs
in this module are by Worker 84.

The shared theorem `extensionDegree_algEquiv`, including its `simp` attribute and proof, is retained from `CompletionWeilTransport` and housed here with the general local Weil extension maps.
