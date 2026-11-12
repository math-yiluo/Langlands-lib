# Full-slice equality under restriction of scalars

Author: Worker 160.

This internal construction for Task 5360 supplies the full test-scheme
comparison needed in the equalizer route to the diagonal of a Weil
restriction. It is derived from the definitions of represented equalizers,
the structural slice maps and pullback uniqueness. Its representability
and finiteness conclusions use the existing Library construction
`quasiAffineWeilRestrictionPresheafIso` and its scheme properties.
The module makes no new assertion from an external source.

For arbitrary schemes `S`, `S'`, `T`, `T'`, fix a cartesian square

```text
T' --f'--> S'
 |          |
 g'         g
 |          |
 v          v
T  --f---> S.
```

No sheaf or algebraic-space assumption is imposed on the full presheaf
`F` over `S'`. The sections `x`, `y` are over Mathlib's chosen pullback
of `T` along `g`. They are thus exactly sections of the restricted
presheaf over `T`.

`sectionEqualizerRepresentationIso` first converts a monomorphic
represented equalizer `j : Y → T` into a natural scheme representation
of `sectionEqualizer x y` on the full slice over `T.left`. The
factorization criterion gives existence of each point and
monomorphicity gives uniqueness. This does not require a sheaf.

In the namespace `WeilRestrictionEqualizer`, `baseTestIso` is the
canonical isomorphism from the specified scheme `T'`, viewed over
`S'`, to the chosen pullback of `T`. Its two projection formulas
specify both maps. `sectionTestMap_comp_baseTestIso` compares the
structural map from a test over `T'` with the pullback of the structural
map from the corresponding test over `T`; the proof tests equality on
the two pullback projections.

`sectionEqualizerWeilIso` applies the original presheaf to that
comparison. It identifies the Weil restriction along `g'` of the
equality locus of the transported upper sections with the equality
locus of `x` and `y` in the original full Weil presheaf along `g`.
Its proof uses the subsingleton criterion for `sectionEqualizer`;
equality of sections can be tested after the isomorphism of the two
base-changed tests. This is natural on all scheme tests.

`sectionEqualizerWeilRepresentationIso` composes this comparison with
a supplied scheme representation of the restriction of a chosen
monomorphic upper equalizer. The chosen upper locus and lower
representing scheme remain explicit.

For `quasiAffineSectionEqualizerWeilIso`, the lower test scheme is
`Spec A`, the upper test scheme is `Spec B`, and `B` is a finite
projective algebra over an arbitrary commutative ring `A`. The old
base schemes and maps remain arbitrary; the square is supplied as
cartesian. The chosen upper locus `Y : Over (Spec B)` is quasi-affine,
locally of finite type over `Spec B`, and has a monomorphic structure
map. It represents equality of the sections transported through
`baseTestIso`, viewed over the old upper base `S'`.

The full representing scheme is precisely the actual
`affineChartWeilRestriction A B Y`. The proof composes the preceding
generic comparison with `quasiAffineWeilRestrictionPresheafIso`.
`exists_quasiCompact_sectionEqualizer_weil` packages that full
representation together with quasi-compactness of its structure map,
obtained from `quasiAffineWeilRestriction_schemeProperties`.

The original presheaf is not assumed representable, to have an atlas,
or to be locally of finite type. Only the upper equalizer locus is
locally of finite type over the upper test base. There is no
Noetherian, field or finite-free hypothesis, no restriction on scheme
tests, and no use of a proof of the algebraic-space Weil
representability statement. This module does not itself construct the
upper equalizer, glue over nonaffine lower tests, or prove closedness;
those are separate geometric steps.
