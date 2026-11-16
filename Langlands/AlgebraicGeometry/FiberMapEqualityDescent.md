# Coefficient enlargement preserving equality on every residue fibre

This is an internal derived application of constructible-set detection on an
actual affine limit. It imports the existing presentation of a ring as the
directed union of its finitely generated subalgebras, and the fibre-map equality
locus. No new external structural theorem is asserted.

For a commutative base ring `R₀`, an `R₀`-algebra `R`, a constructible subset `s`
of `Spec R₀`, and a finite set `t` of elements of `R`, suppose the inverse image
of `s` is the whole of `Spec R`. Then
`exists_fg_subalgebra_preimage_eq_univ` supplies a finitely generated
`R₀`-subalgebra `T` of `R` containing `t` for which the inverse image of `s`
is already the whole of `Spec T`.

The proof orders all finitely generated subalgebras containing `t` by inclusion.
They form a nonempty directed system exhausting `R`. Its actual spectrum cone
is a limit by the imported subalgebra-stage result. Pull `s` back to one stage;
its inverse image is constructible and has full inverse image at the limit.
Constructible affine-limit detection supplies an incoming stage with full inverse
image. Compatibility of the structure maps identifies that image with the
original condition over the new coefficient algebra.

When `R₀` is noetherian and `A` and `B` are finite type `R₀`-algebras,
`exists_fg_subalgebra_fiberMapEquality` applies this to two algebra maps
`f,g : A → B`. If their scalar extensions to `R` agree on every actual residue
fibre, their scalar extensions to some finitely generated `T` containing `t`
already agree on every actual residue fibre. This uses constructibility and the
full inverse-image base-change identity for the equality locus.

`FiberEqualityCoefficientModel` retains the actual subalgebra, its finite
generation, the inclusion of `t`, and the full fibre-equality condition.
`fiberEqualityCoefficientModel` chooses the model just proved to exist. The
noetherian ring, its algebra, and the two finite type algebras inhabit a common
arbitrary universe. Nilpotents are retained in every tensor algebra; `R` need
not be noetherian or reduced. The empty-spectrum case is included.

This result preserves equations for already supplied finite type algebras and
maps. Constructing reductive group-scheme coefficient models and identifying
the central-fibre commutation equations remain further steps. Global kernel
centrality and the full central-isogeny criterion are not asserted here.
