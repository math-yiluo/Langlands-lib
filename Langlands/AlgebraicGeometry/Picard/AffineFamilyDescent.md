# Descent of actual Picard families over affine bases

This internal adapter uses the published theorem
`NoetherianApproximation.lineBundleSubalgebraDescent` and the actual Picard
pullback pseudofunctor. It adds no external mathematical input.

For commutative rings `R` and `A` in an arbitrary universe `u` and an
`R`-algebra structure on `A`, `affineBase R A` is the object
`Spec A → Spec R` of the full scheme slice. For a subalgebra `B ⊆ A`,
`affineSubalgebraMap B` is the canonical slice arrow `Spec A → Spec B`.

`PicardGroupoid.exists_affineFamily_subalgebra` takes a quasi-compact,
quasi-separated morphism `f : X → Spec R`, an actual line bundle `M` on
`Spec A ×[Spec R] X`, and any finite set `s` of elements of `A`. It produces
a finitely generated `R`-subalgebra `B` containing `s` and an actual line
bundle `L` on `Spec B ×[Spec R] X`. Its conclusion includes an isomorphism
in the actual Picard groupoid from the ordinary pseudofunctor pullback
of `L` along `affineSubalgebraMap B` to `M`.

The proof applies the published subalgebra descent theorem to the flipped
pullback square of the actual family. That theorem supplies a module on the
oppositely ordered chosen fibre product `X ×[Spec R] Spec B`. Pullback by
`relativeSpaceSymmetry` gives `L` on the actual relative space. The composite
of the relative-space map with this symmetry satisfies the two projection
equations required by descent. The ordinary module pullback composition
isomorphism then gives the comparison to `M`. `ObjectProperty.isoMk` and
`Core.isoMk` retain this isomorphism in the line-bundle subcategory and its
core.

This result establishes finite-type subalgebra descent on objects, with an
actual comparison isomorphism. It does not descend a specified arrow between
families or assert a category equivalence with a filtered limit. Smooth
chart construction and the Picard atlas theorem remain separate obligations.
