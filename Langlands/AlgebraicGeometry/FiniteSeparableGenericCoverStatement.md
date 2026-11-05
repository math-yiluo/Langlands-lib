# A finite étale cover with prescribed generic residue field

`FiniteSeparableGenericCover` records a derived intermediate assertion in
the proof of Stacks Lemma 37.24.8 (0551). It concerns an arbitrary actual
irreducible scheme `Y`, a whole-space generic point `η`, and a prescribed
finite separable extension `L` of the actual residue field `Y.residueField η`.
It asks for a nonempty open `V` and an irreducible affine scheme `Y'` with
an actual finite étale surjective map `g : Y' ⟶ V.toScheme`.

The chosen whole-space generic point `η'` of `Y'` comes with an actual
scheme isomorphism
`e : Spec L ≅ Spec (Y'.residueField η')`.
The displayed equality of scheme morphisms states that the composite
from `Spec L`, through this isomorphism, the actual residue-field map to
`Y'`, and `g` and the open immersion into `Y`, equals the composite through
`Spec (Y.residueField η)` induced by the given extension's algebra map.
Consequently the isomorphism retains the specified extension over the
original generic point; it is not merely an abstract isomorphism of fields.
All fields and schemes lie in the same arbitrary universe `u`.

This assertion isolates the source proof's construction after a finite
separable extension has already been selected. In a nonempty affine open,
the source lifts a monic primitive-element polynomial from the generic
residue field. Its quotient is finite free, has a unique prime over the
base's nilradical with the prescribed residue extension, and is étale
there. Finite closed-image shrinking makes the whole cover étale. The
statement records the resulting generic-field identification as an
isomorphism of spectra and its compatible structural triangle.

Source: registered collection
`stacks-generic-geometric-irreducibility-2026-11-04`, `0551.html`,
Lemma 37.24.8, proof beginning with a nonempty affine open and the chosen
finite separable extension. Collection SHA-256:
`7779fd83e268ecb0b8a0b8783d039fea6de1ccf33ce652f9bf972c9697b02f8c`;
individual HTML SHA-256:
`90c09df79311d4ad6ea562a3d1813e14cab5b794702822c5e5a81131ab8af6e0`.
The retained original includes the corrected nilradical wording. This
intermediate assertion is extracted from that proof, rather than quoted
as a separately numbered Stacks theorem.

No reducedness, Noetherianity, quasi-separatedness, or characteristic
hypothesis is imposed on `Y`. This pair defines a proposition only. It
constructs neither the prescribed cover nor a splitting field, and does
not prove the exact generic-component splitting target by itself.
