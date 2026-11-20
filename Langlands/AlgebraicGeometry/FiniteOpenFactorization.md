# Finite open factorization over an affine scheme

Let `f : X ⟶ Y` be a separated, quasi-compact, locally quasi-finite morphism
locally of finite type, with `Y` affine. A `FiniteOpenFactorization f` consists
of an affine spectrum, an open immersion from `X` into that spectrum, and a
finite morphism from it to `Y` whose composite is `f`.

Mathlib's Zariski Main Theorem gives an open immersion into the relative
normalization, which is affine and integral over `Y`. A finite family of
principal opens inside the image of `X` covers the image. The coordinate
algebra of each principal open is of finite type over the base by identifying
it with the sections of the corresponding affine open of `X`. Adjoin the
principal elements and the numerators of finitely many generators of each
localized algebra to the base. The resulting subalgebra is of finite type
and agrees with the normalization after inverting each chosen principal
element. Every element of the subalgebra is integral over the base, so
the subalgebra is module-finite.
The localization criterion for the open map from a quasi-affine scheme
into an affine spectrum proves that `X` embeds openly in this finite model.
The section maps identify the composite with `f`.

This is the affine-target finite factorization form of Zariski's Main
Theorem. It is derived from Mathlib's relative normalization form and the
Library's principal-open approximation and localization arguments. The
ring argument is the relative-base version of the finite-subalgebra
construction in `AbsoluteNoetherianApproximation.AwayBijective`.
