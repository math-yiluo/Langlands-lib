# Actual fixed schemes of affine multiplicative-group actions

This internal construction extends the coordinate equations of
`AffineGmAction.lean` to actual closed fixed schemes. For an arbitrary affine
scheme `X` over `Spec R` and an actual multiplicative-group action, its fixed
scheme is the relative spectrum of the chosen coordinate algebra modulo the
fixed coefficient ideal. The inclusion is a closed immersion into the original
supplied `X`.

The ideal-factorization criterion is first proved on affine algebra spectra
using the quotient algebra's universal property and the actual coordinate
point equivalence. The coefficient criterion from `AffineGmAction` then
identifies this with all-refinement fixedness. Transport along the coordinate
isomorphism gives factorization on any affine relative test. On a general
relative test, factorization is obtained on its affine open cover. Uniqueness
of lifts through the closed monomorphism permits gluing. Thus
`exists_schemeActionFixed_factor_iff_all` retains all relative test schemes.
The inclusion itself satisfies all-refinement fixedness.

When `X` is smooth over `Spec R`, the constructed fixed scheme is smooth over
`Spec R`. The coordinate comparison transfers smoothness to the coordinate
algebra. The published fixed-quotient lifting and finite-equation argument gives
smoothness of its quotient over an arbitrary commutative base ring; the spectrum
criterion transfers this back to the actual fixed scheme.

The construction generalizes the fixed-scheme method in
`Torus/RelativeTransporterSmooth.lean` to arbitrary affine target schemes and the
actual chosen multiplicative group. Its general closed quotient helpers are
internal affine geometry. No external theorem is newly transcribed. This unit
does not yet construct attracting schemes or prove the properness target.
