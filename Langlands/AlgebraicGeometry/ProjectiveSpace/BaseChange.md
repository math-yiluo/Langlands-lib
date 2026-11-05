# Base change of polynomial-projective embeddings

This module derives explicit base-change embeddings and properness from the
Library's polynomial-Proj projective space. It works over arbitrary commutative
rings `R` and `B` in the same universe with an `R`-algebra structure on `B`.
There are no field, flatness or Noetherian assumptions.

`ProjectiveSpace.baseChangeMap R B n` is the existing polynomial-Proj map.
`baseChangeMap_isPullback` identifies its square with the structure morphisms
to `Spec B` and `Spec R` as a pullback, reusing the published theorem
`AlgebraicGeometry.ProjSpace.isPullback_map`.

Suppose a specified square presents `X'` with maps `a : X' → X` and
`b : X' → Spec B` as the base change of `p : X → Spec R`. For a specified
`i : X → ProjectiveSpace R n` with `i ≫ projectiveSpaceToSpec R n = p`,
`baseChangeLift sq i hi` is the actual unique morphism to projective space
over `B` obtained by the projective-space pullback universal property. Its two
projection identities are proved as `baseChangeLift_toSpec` and
`baseChangeLift_map`. Pullback cancellation proves
`baseChangeLift_isPullback`; stability of closed immersions under base change
then proves the closed-immersion instance for the lifted map.

`IsHProjective.of_isPullback` applies this construction to an existing
H-projective witness, retaining its projective dimension. The conclusion
concerns the specified `b`, rather than a replacement scheme.
`IsHProjective.isProper` composes the existing closed immersion with the
published proper structure map of finite polynomial projective space.

These are internal deductions from the cited Library constructions and Mathlib's
pullback and morphism-property theorems. They do not establish representability
or supply an initial projective embedding.
