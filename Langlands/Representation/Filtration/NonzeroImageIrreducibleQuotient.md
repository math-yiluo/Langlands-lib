# A whole irreducible quotient from a nonzero image

Authors: Worker 320 (original draft), Worker 514 (import reduction and verification).

This internal algebraic lemma is derived from the Noetherian part of finite
group-algebra length. For a nonzero morphism from a finite-length smooth
representation `A` to `B`, its actual image has finite length and is nonzero.
A maximal proper group-algebra submodule of that image gives a simple quotient
`C`. The composite map from `A` onto `C` is surjective, so `C` is a quotient of
the whole source. The inclusion of the image into `B` also witnesses that `C`
is an actual subquotient of `B`.

The construction is elementary module theory, using Mathlib's coatomicity and
simple-quotient criteria. Its intended application is the image step in
Jantzen (1997), Lemma 5.5, printed pages 1226–1227, registered source
`jantzen-1997-supports-classical`. This lemma does not use parabolic induction
or any classification result.

The Lean witness is the image subrepresentation `(hom f).range` and its
quotient by the chosen coatom; reflexivity supplies the required isomorphism.
Only `Category.Subquotients` is imported, so this helper has no dependency on
classification or cuspidal-support results.
