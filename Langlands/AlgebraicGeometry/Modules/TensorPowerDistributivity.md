# Distribution of actual sheaf tensor powers

For every `X : AlgebraicGeometry.Scheme.{u}`, arbitrary module sheaves
`M N : X.Modules`, and `k : ℕ`, this module constructs

```lean
Langlands.Scheme.Modules.tensorPowTensorIso (M N : X.Modules) (k : ℕ) :
  tensorPow (tensorObj M N) k ≅ tensorObj (tensorPow M k) (tensorPow N k)
```

All names in this display are in `Langlands.Scheme.Modules`.
The tensor is the published `tensorObj`, obtained by sheafifying the
sectionwise tensor. The unit is the existing `structureSheaf X`, and
`tensorPow` is the existing right-associated recursion, including its
final unit factor. These definitions are imported unchanged.
No geometric hypotheses are needed.

## Tensor helpers

`tensorMapIso e d` applies the existing `tensorFunctor X` to the product
isomorphism `e.prod d`. Its forward and inverse maps are respectively
`tensorMap e.hom d.hom` and `tensorMap e.inv d.inv`, as recorded by
`tensorMapIso_hom` and `tensorMapIso_inv`. Its inverse laws follow from
the functor's identity and composition laws.

`tensorMiddleFourIso A B C D` has endpoints

```text
(A tensor B) tensor (C tensor D)
    ≅ (A tensor C) tensor (B tensor D).
```

Its implemented composite follows these steps:

1. Apply `tensorAssociator A B (tensorObj C D)` to obtain
   `A tensor (B tensor (C tensor D))`.
2. Inside the second factor, invert `tensorAssociator B C D`,
   swap `B` and `C` with `tensorComm B C`, and apply
   `tensorAssociator C B D`. This gives
   `A tensor (C tensor (B tensor D))`.
3. Invert `tensorAssociator A C (tensorObj B D)` to obtain the target.

The associator is the published comparison of the actual tensor with
the symmetric monoidal structure obtained by sheafification localization.
The swap is the published sheafification of presheaf symmetry.
Every step is an already constructed isomorphism, so the composite
supplies its inverse and both inverse laws.

## Recursion and equations

Write `d_k` for `tensorPowTensorIso M N k`.
At zero, the endpoints reduce to
`structureSheaf X` and its actual tensor square.
The definition is exactly
`(tensorLeftUnitor (structureSheaf X)).symm`.
Thus `d_0.hom` is the inverse left unitor and `d_0.inv` is its forward
map. These descriptions are exported by `tensorPowTensorIso_zero`,
`tensorPowTensorIso_zero_hom`, and `tensorPowTensorIso_zero_inv`.

At successor the source reduces to
`(M tensor N) tensor (tensorPow (tensorObj M N) k)`.
First apply `tensorMapIso (Iso.refl (tensorObj M N)) d_k`.
The result is
`(M tensor N) tensor (tensorPow M k tensor tensorPow N k)`.
Then apply
`tensorMiddleFourIso M N (tensorPow M k) (tensorPow N k)`.
Its target is definitionally the tensor of the two successor powers.

`tensorPowTensorIso_succ` gives this exact isomorphism equation.
`tensorPowTensorIso_succ_hom` gives the forward composite
`tensorMap (𝟙 _) d_k.hom` followed by the middle-factor exchange.
`tensorPowTensorIso_succ_inv` gives the reverse composite: the inverse
middle-factor exchange followed by `tensorMap (𝟙 _) d_k.inv`.
The isomorphism equations and zero map equations are proved by `rfl`.
The successor map equations simplify the isomorphism equation with the
composition and tensor-map projections. Their elaboration uses a finite
local recursion-depth limit of 2048 to handle the expanded sheaf tensor types.

## Provenance and scope

Worker 692 authored this derived categorical infrastructure. Its intended
use is the product section in the proof of Stacks Project Lemma 28.27.5,
in [Section 28.27, tag 01PR](https://stacks.math.columbia.edu/tag/01PR).
The registered source is
`stacks-ampleness-tensor-isomorphism-2026-10-24`,
*Stacks Project - Ampleness tensor and isomorphism transport (HTML snapshot
2026-10-24)*, retained as
`literature/Stacks Project - Ampleness tensor and isomorphism transport (HTML snapshot 2026-10-24)/01PR.html`.
The registered directory SHA256 is
`23bfc9d1d2b4467556c7308dd203f22596c80d2f5276f1d5f9829673427e2f2d`.
The retained section, including the proof of Lemma 28.27.5 and its comments,
was read. No source-specific errata file was present in the workspace,
current Library, or project `notes/errata/` locations on 2026-10-26.
The live section and its five comments were also checked on that date;
the comments contain no correction relevant to this construction.
That current check is retained as registered source
`stacks-01pr-current-errata-check-2026-10-26`,
`literature/Stacks Project - 01PR current source and comments (HTML snapshot 2026-10-26).html`,
SHA256 `10e5729facc1f46a826ad3adad02c107aa2d7aec3f87b7650122c46c5d9a59c1`.

The literature proof forms a product from powers of two sections and
regards it as a section of a power of the tensor product. The present
declaration supplies only the underlying distribution isomorphism,
in the direction from the power of the tensor to the tensor of the powers.
Its inverse is available for transporting such a product section.
The exact declaration and its extension to arbitrary module sheaves and
the zeroth power are internal categorical constructions, rather than a
literal statement of that literature lemma.

This file imports `TensorCoherenceMaps`, reusing its actual associator
and the published tensor and monoidal localization infrastructure.
It assumes no pending coherence proposition, pullback comparison, or
rank-one theorem. It does not construct powers of sections, flatten
iterated powers, compare section loci, or prove ampleness.
No naturality theorem for `tensorPowTensorIso` is asserted in this unit.
The pinned environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
(Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`).
