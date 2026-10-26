# Generic flatness for finite morphisms

`Langlands.AlgebraicGeometry.FiniteGenericFlatStatement.{u}` is a
proposition-valued definition in the module
`Langlands.AlgebraicGeometry.FiniteGenericFlatStatement`. It states a
specialization of the Stacks Project's generic flatness proposition, Tag
[052A](https://stacks.math.columbia.edu/tag/052A), Proposition 29.28.1.
This file supplies a statement only; it does not prove generic flatness.

## Exact statement

For every pair of schemes `X Y : Scheme.{u}` and morphism `f : X ⟶ Y`,
assume:

1. `IsIntegral Y`: the target is integral. Mathlib's definition includes
   nonemptiness and requires the section ring on each nonempty open to be an
   integral domain; in particular, the underlying space is irreducible.
2. `IsLocallyNoetherian Y`: every affine open of the target has a Noetherian
   coordinate ring. The target is not required to be quasi-compact.
3. `IsFinite f`: the inverse image of each affine target open is affine,
   and the induced ring homomorphism is finite, meaning that its target ring
   is a finite module over its source.

The conclusion is
`∃ U : Y.Opens, Set.Nonempty (U : Set Y) ∧ Flat (f ∣_ U)`.
Here `U` is an open subset of the target with at least one point.
Mathlib's `morphismRestrict`, written `f ∣_ U`, is the actual morphism
from the open subscheme on `f ⁻¹ᵁ U` to the open subscheme on `U`.
It identifies, via `pullbackRestrictIsoRestrict`, with the base change
`X ×_Y U → U`; see also `isPullback_morphismRestrict`.
`Flat` is Mathlib's scheme-morphism property, equivalently flatness of all
the induced local-ring maps (`Flat.iff_flat_stalkMap`).

All hypotheses are ordinary proposition arguments using Mathlib definitions.
The universe `u` is arbitrary. The source need not be integral or nonempty,
and the morphism need not be surjective. There is no hypothesis of flatness,
constant rank, a locally free direct image, or a supplied generic-freeness
witness. The open is existentially quantified, without a canonical choice,
and the conclusion concerns the restricted morphism, not global flatness.

## Source specialization and provenance

Proposition 29.28.1 assumes an integral base, a finite type morphism, and a
quasi-coherent module of finite type on the source. It produces a dense open
base over which both the morphism and the module have flatness and finite
presentation properties.

Apply its mathematical statement with base `Y` and module `𝒪_X`, which is
quasi-coherent and of finite type as a module over itself. A finite morphism
is of finite type: it is quasi-compact and locally of finite type.
The additional hypothesis `IsLocallyNoetherian Y` restricts this
specialization and is available in the intended application; the cited
proposition does not require it. Retain only flatness of the restricted
morphism. The dense open in the source proposition is nonempty because
the integral base is nonempty. Conversely, any nonempty open of an integral
base is dense, though density is not an additional field of this Lean
conclusion. The module and finite presentation conclusions are omitted.

The original proof passes to an affine integral base and a finite affine
cover of the source, then applies generic freeness to the relevant modules
and modules describing overlap complements. Localizing at a product of
nonzero elements gives the desired open. This describes the cited source's
proof; no part of that proof is implemented in this statement module.

The exact interface and source specialization were supplied in Worker 415's
task specification. The declaration and explanation preserve that scope.
A proof of this published proposition is a separate task.

## Retained original

- Source ID: `stacks-generic-flatness-052A-2026-10-25`.
- File: `literature/Stacks Project — Generic flatness, Tag 052A (HTML snapshot 2026-10-25).html`.
- Locator: Proposition 29.28.1, Tag 052A, full statement and proof.
- SHA256: `bcd24c1b8433a6c2f781d325ed27ad9a7d73e302a226adf94ad03e376c5fd894`.

The full proposition and proof were read. The retained page has no comments,
and no project errata file for this registered source was found.
