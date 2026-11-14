# Extending an isomorphism of field fibres of two split tori

This internal module extends the published field-fibre automorphism construction
in `HenselianNormalizerLifting` to an isomorphism between two split tori. It is
derived from the integral exponent maps and character maps of
`ExponentHomomorphisms`, and the standard split-torus base-change isomorphisms.
No new source transcription is asserted.

All types and schemes use an arbitrary common universe `u`. The field `k` has
arbitrary characteristic. The base `S` is any scheme, and
`b : Spec k → S` is any field point. The two actual commutative group schemes
`T` and `T'` over `S` are split tori. The base need not be connected, reduced,
local, or Henselian.

`splitTorus.fieldCommIsoExtension` takes an actual isomorphism of standard
split tori over `k`, with finite coordinate types `I` and `J`. It returns an
actual isomorphism of the standard commutative split tori over `S`. Its hom
and inverse are the exponent homomorphisms of the integral character maps of
the original hom and inverse. The integral matrices can have different index
types. Functoriality of character maps, the two inverse identities, and
`exponentHom_comp` prove that these maps are inverse.

`splitTorus.fieldCommIsoExtension_baseChange` proves exact recovery of the
supplied hom after pullback along `b`, using the specified standard split-torus
comparison isomorphisms. It applies `exponentHom_baseChange` and
`exponentHom_characterMap`. Its right side is the original group-scheme hom
read in the commutative group-scheme category by `Additive.ofMul`.

`IsSplitTorus.iso_fieldBaseChange_surjective` states that the map

    (T ≅ T') → (T_k ≅ T'_k),   e ↦ (CommGroupScheme.baseChange b).mapIso e

is surjective. Thus every specified actual isomorphism of field fibres extends
to an actual isomorphism over `S`, and its pullback is exactly the given
isomorphism. The theorem does not assert uniqueness over arbitrary bases.

The proof chooses splittings of `T` and `T'`, converts the fibre isomorphism
into a map between standard coordinate tori, applies `fieldCommIsoExtension`,
and conjugates back by the chosen splittings. The base-change equality above
and cancellation of these splitting maps prove equality of isomorphisms.
The result concerns actual group-scheme maps, with their equality on all tests;
it makes no comparison based solely on rational points.

This is a supporting extension step for integral torus conjugacy. It supplies
neither a residue conjugating point nor an ambient integral conjugating point,
and by itself gives no apartment containment or fixed-pair theorem.
