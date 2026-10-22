# The local Weil group of an extension as an open subgroup

Author: Worker 53. This is a definition and construction contribution.

## Content

Fix a prime `p`, two `PadicField` objects `F` and `E` in independent
universes, and an algebra homomorphism `f : F.Carrier →ₐ[Padic p] E.Carrier`,
the abstract form of a finite extension `E / F`. Write
`j = extensionWeilMap F E f : W_E →ₜ* W_F` for the published map of actual
local Weil groups (module `Langlands.Weil.Local.ExtensionWeil`), and `n` for
the published degree `extensionDegree F E f = [E : F]`.

Tate defines `W_E` as a subgroup of `W_F`. Here `E` is an abstract field with
an embedding, so `W_E` is a separate group and the subgroup of `W_F` is the
image of `j`. This module packages that image and its identification with
`W_E`, so that constructions on subgroups of `W_F` can be used for `W_E`.

- `extensionWeilRange` is the subgroup `j(W_E)` of `localWeilGroup F`, the
  range of `j` as a monoid homomorphism. It carries the subspace topology
  inherited from `W_F`.
- `extensionWeilRangeEquiv : localWeilGroup E ≃ₜ* extensionWeilRange F E f`
  is `W_E` identified with that subgroup as a topological group. The group
  isomorphism is Mathlib's `MonoidHom.ofInjective` for the published
  injectivity `extensionWeilMap_injective`. The forward map is continuous
  because `j` is. The inverse is continuous because `j` is a topological
  embedding (published `extensionWeilMap_isEmbedding`): a map into `W_E` is
  continuous when its composite with `j` is, and that composite is the
  subtype inclusion of the image.
- `extensionWeilRangeEquiv_apply` states that the forward map is `j`.
  `extensionWeilMap_extensionWeilRangeEquiv_symm` states that `j` sends the
  inverse image of an element of the subgroup back to that element.
- `localProjection_extensionWeilRange` states that on the subgroup the
  projection `W_F → G_F` equals the published Galois map
  `extensionGaloisMap F E f` applied to the projection `W_E → G_E` of the
  corresponding element. It is the published
  `localProjection_extensionWeilMap` transported through the identification.
- `localNormCharacter_extensionWeilRange` states that on the subgroup the norm
  character of `F` equals the norm character of `E` of the corresponding
  element. It is the published `localNormCharacter_extensionWeilMap`
  (`ν_F ∘ j = ν_E`) transported through the identification.
- `extensionWeilOpenSubgroup` is the same subgroup as an `OpenSubgroup` of
  `W_F`. Openness is the published `extensionWeilMap_range_isOpen`.
- `extensionWeilRange_index` states that the subgroup has index `n = [E : F]`
  (published `extensionWeilMap_range_index`). The instance
  `extensionWeilRange_finiteIndex` records finite index for typeclass search
  (published `extensionWeilMap_range_finiteIndex`).
- `localInertia_inf_extensionWeilRange` proves
  `I_F ⊓ j(W_E) = j(I_E)`: the inertia of `F` meets the subgroup exactly in the
  image of the inertia of `E`. An element `j w` of the subgroup lies in `I_F`
  exactly when `w` lies in `I_E`, by the published
  `extensionWeilMap_mem_localInertia`.

## Choices and scope

Everything here is built from the published `extensionWeilMap`. That map
depends on the choice-based closure lift behind the published
`extensionGaloisMap`, so the subgroup and the identification depend on the
same choices. No canonicity is claimed. This module proves only the
direction of Tate (1.4.5) already published in `ExtensionWeil`: each `W_E` is
an open subgroup of finite index. It does not prove that every open subgroup
of finite index arises this way. It does not define restriction or induction
of representations or parameters along `j`; those are separate obligations.

## Sources

This is a derived repackaging of the finite-extension structure of local Weil
groups in John Tate, *Number theoretic background*, Corvallis Part II
(1979), registered source `tate-1979-number-theoretic-background`,
SHA-256 `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.

- (1.1), printed page 3 (PDF page 12): `W_E = φ⁻¹(G_E)` is a subgroup of
  `W_F`, open because `φ` is continuous, with
  `W_F / W_E ≅ G_F / G_E ≅ Hom_F(E, F̄)`. Here `extensionWeilRange` is that
  subgroup, `extensionWeilRangeEquiv` identifies it with the separately
  constructed `W_E`, and the index statement is the cardinality form of the
  bijection.
- (1.4.5), printed page 7 (PDF page 16): the subgroups `W_E` are open of
  finite index. `extensionWeilOpenSubgroup` and the finite-index instance
  record this direction.
- (1.4.6), printed page 7 (PDF page 16): the restriction of the norm function
  from `W_F` to the subgroup `W_E` is the norm function of `W_E`. This is
  `localNormCharacter_extensionWeilRange` for the published complex norm
  characters.

The inertia statement `localInertia_inf_extensionWeilRange` is the derived
subgroup form of the published inertia pullback `I_E = j⁻¹(I_F)`. That
pullback holds because `j` multiplies the geometric degree by the residue
degree, which is positive. These passages were read in the retained PDF.

## Dependencies

The only project import is `Langlands.Weil.Local.ExtensionWeil`, published at
Library commit `22b4f024e0d4218752e970d09329d1799f6d81d1`. Its declarations
`extensionWeilMap`, `extensionWeilMap_injective`, `extensionWeilMap_isEmbedding`,
`extensionWeilMap_range_isOpen`, `extensionWeilMap_range_index`,
`extensionWeilMap_range_finiteIndex`, `extensionWeilMap_mem_localInertia`,
`localProjection_extensionWeilMap` and `localNormCharacter_extensionWeilMap`
are used by Lean name. Pinned Mathlib supplies `MonoidHom.ofInjective`,
`MonoidHom.apply_ofInjective_symm` and `Topology.IsInducing.continuous_iff`.
The environment is Lean 4.34.0 with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. All declarations and proofs in
this module are by Worker 53.
