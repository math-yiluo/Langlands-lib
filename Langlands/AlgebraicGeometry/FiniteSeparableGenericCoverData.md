# Prescribed generic extensions over arbitrary irreducible schemes

This is a derived construction for the prescribed generic extension step
in the proof of Stacks Lemma 37.24.8 (0551). The source first passes to a
nonempty affine open, constructs a monic finite free model of a prescribed
finite separable extension, and then shrinks until the resulting cover is
finite étale. This module transports the previously constructed affine
cover back to the original arbitrary irreducible scheme, keeping its
actual generic residue field and the original extension map.

Source: registered collection
`stacks-generic-geometric-irreducibility-2026-11-04`, `0551.html`,
Lemma 37.24.8, proof from the choice of a nonempty affine open through
finite étale shrinking. Collection SHA-256:
`7779fd83e268ecb0b8a0b8783d039fea6de1ccf33ce652f9bf972c9697b02f8c`;
individual HTML SHA-256:
`90c09df79311d4ad6ea562a3d1813e14cab5b794702822c5e5a81131ab8af6e0`.
The retained original includes the corrected nilradical wording.

## Actual data and constructor

`PrescribedGenericCoverData Y η L` records an actual nonempty open `V` of
`Y`, an affine irreducible scheme `Y'`, and an actual finite étale
surjective morphism `g : Y' ⟶ V.toScheme`. Its chosen point `η'` is generic
for the whole space `Y'`. Its field comparison is an actual scheme
isomorphism

```text
e : Spec L ≅ Spec (Y'.residueField η').
```

The recorded triangle is

```text
e.hom ≫ Y'.fromSpecResidueField η' ≫ g ≫ V.ι
  = Spec.map (algebraMap (Y.residueField η) L)
      ≫ Y.fromSpecResidueField η.
```

Here both residue fields are Mathlib's actual stalk residue fields.
The displayed map on the right uses the supplied algebra action on `L`.

`PrescribedGenericCoverData.nonempty` proves that these data exist when
`Y` is irreducible, `η` is a whole-space generic point, and `L` is finite
dimensional and separable over `Y.residueField η`.
`PrescribedGenericCoverData.construct` chooses the data from this theorem.
The scheme, both fields, and the rings used in its construction lie in one
arbitrary common universe `u`. There are no Noetherianity, reducedness,
quasi-separatedness, or separatedness hypotheses on `Y`, and no model
existence premise.

## Implemented construction and compatibility

`chartResidueFieldIso` compares the ideal residue field at a point `p` of
an affine open chart `f : Spec R ⟶ Y` with `Y.residueField η`, given
`f p = η`. It composes Mathlib's comparison between scheme and ideal
residue fields, the inverse of the open immersion's residue-field map,
and the residue-field isomorphism of equal points.
`chartResidueFieldIso_triangle` proves that this comparison followed by
the affine coefficient map and `f` is precisely
`Y.fromSpecResidueField η`. Its proof uses the coefficient identity for
the scheme/ideal comparison and naturality of the residue-point map.

For `nonempty`, an affine chart containing `η` is nonempty and
irreducible. Its nilradical is prime and is its generic point; uniqueness
of generic points shows that this prime maps to the specified `η`.
The chart comparison transports the fraction-field structure of
`(R / nilradical R)` onto the actual field `Y.residueField η`.
The proof keeps the given action from that field to `L` and defines the
quotient-ring actions by composition, with explicit scalar-tower
identities. In particular, it does not assert that `R` itself embeds in
its generic residue field.

The proved `finiteSeparableNilradicalEtaleModel` constructor and
`FiniteSeparableNilradicalEtaleScheme` provide the actual affine
irreducible cover of a nonempty principal open of `Spec R`, together
with its generic residue-field isomorphism and coefficient triangle.
Composing that principal-open inclusion with `f` gives an open immersion
`j` into `Y`. Set `V = j.opensRange`. The canonical isomorphism from the
principal open onto `V.toScheme` transports the cover and its finite,
étale, and surjective properties. A point of the original principal
open witnesses nonemptiness of `V`.

The final triangle follows by composing the affine model's coefficient
triangle with `f` and applying `chartResidueFieldIso_triangle`.
Consequently the construction realizes the prescribed extension over
the original generic point, with its specified structural map.

## Scope

This unit constructs the cover for an already supplied finite separable
extension. It does not choose a field extension splitting the geometric
components of a given generic fibre, prove that splitting property,
or prove the full Stacks 0551 component conclusion. Those remain
separate inputs to its application. It also makes no claim to complete
Conrad's filtered fibre descent or the whole adelic-points program.
