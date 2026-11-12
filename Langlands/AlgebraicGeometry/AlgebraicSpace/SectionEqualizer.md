# Equality of sections on the full slice

Author: Worker 160.

This is an internal categorical construction for the represented equalizer
route in Task 5360. It is derived from the definitions of slice categories,
presheaves and sheaf separatedness, and does not assert a new source theorem.
All base schemes, presheaves and test schemes are arbitrary.

For `T : Over S` and sections `x y : F(T)`, `sectionTestMap U` is the
structural map from a scheme `U` over `T.left` to `T`, viewed over `S`.
Its naturality states that composing with a map of test schemes gives the
same structural map.

`sectionEqualizerSubfunctor x y` is the subfunctor of the represented
terminal object on `Over T.left` whose points satisfy equality of the
pullbacks of `x` and `y` along that structural map.
`sectionEqualizer x y` is its underlying full presheaf. Each value is a
subsingleton: there is at most one map to the terminal object. If `F` is an
fppf sheaf, `isSheaf_sectionEqualizer` proves that this equality presheaf
is an fppf sheaf, using separatedness of `F` after restriction to `T.left`.

`sectionEqualizerIsoOfIff` identifies any subterminal presheaf with this
equality presheaf if inhabitation of its values is equivalent to equality
of those pullbacks. The forward map uses the unique structural arrow;
the inverse chooses an inhabitant, and subsingletonness proves all
naturality and inverse laws.

`sectionEqualizerRestrictIso` compares restriction along an arbitrary
scheme morphism `j : U → T.left` with the equality presheaf of the
restricted sections. The proof compares the two structural composites.
No affine, finiteness or openness hypothesis is imposed on `j`.

Finally, a scheme representation over `T.left` gives a monomorphic
structure map (`mono_of_sectionEqualizerIso`) and a representation of the
original equalizer over `S`
(`representsEqualizer_of_sectionEqualizerIso`). The monomorphism proof
views two maps with equal composites as maps from the same slice object
and uses injectivity of the representing isomorphism. The factorization
criterion in `RepresentsEqualizer` follows by applying the representation
to the scheme over `T.left` defined by an arbitrary map to `T`. This
retains every scheme test in the original slice.
