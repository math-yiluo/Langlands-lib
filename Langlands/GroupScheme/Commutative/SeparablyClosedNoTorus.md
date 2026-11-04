# Cocharacters and commutative unipotence over separably closed fields

This internal module combines the coefficient-descent and actual scheme-pullback
constructions in `Torus.CocharacterBaseChange` with the algebraically closed
commutative character criterion in `Commutative.NoTorus`. All fields and schemes
in a declaration have the same arbitrary universe `u`.

`cocharacterEquivOfIsPurelyInseparable Z K` constructs an equivalence between
the actual homomorphism sets `Hom(Gm_k, Z)` and `Hom(Gm_K, Z_K)`, where `Z_K`
is the actual scheme pullback, `Z` is affine and locally of finite type over `k`,
and `K/k` is purely inseparable. It conjugates the diagonalizable-homomorphism
equivalence by the standard isomorphisms from `Gm` to the diagonalizable group
with exponent group `PUnit → ℤ`. The equivalence in the imported module extends
coefficients of universal image points, compares those points with the actual
pullback, and reconstructs homomorphisms. No separate identification with
functorial base change through a source isomorphism is claimed here.
`cocharacterEquivOfIsPurelyInseparable_zero` follows from preservation of zero
by the imported equivalence and by composition. These constructions need
neither smoothness nor connectedness.

`isUnipotent_of_gm_hom_eq_zero_of_isSepClosed` proves that a smooth connected
affine commutative group `Z` over a separably closed field is unipotent if every
actual homomorphism `Gm → Z` is zero. The algebraic closure is purely inseparable
over a separably closed field, by Mathlib's algebraic-extension instance.
The imported cocharacter-vanishing theorem therefore gives vanishing over the
algebraic closure. The actual pullback remains smooth and affine, and the
published geometric-connectedness theorem for connected finite type group
schemes gives its connectedness. The existing algebraically closed commutative
criterion now proves unipotence of the pullback. The published
`IsUnipotent.of_baseChange` reflects unipotence to the original affine group.

`isUnipotent_of_no_torus_of_isSepClosed` specializes to trivial all-test range
for every homomorphism from a torus. It applies this hypothesis to `Gm` and
uses the existing range-zero lemma to obtain zero cocharacters.

The new unipotence statements assume that the field is separably closed.
They do not assert a commutative no-cocharacter criterion over an arbitrary
field, where an anisotropic torus would violate such a criterion. They are
supporting results for the arbitrary-field no-torus theorem, which is not
proved in this module. No maximal-torus base-change theorem or unconditional
no-torus reduction is used.
