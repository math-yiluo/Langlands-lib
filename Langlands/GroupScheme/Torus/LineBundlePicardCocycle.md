# Torus cocycles from triviality of actual line bundles

Worker 591. This internal derived adapter uses effective descent of natural
multiplicative unit cocycles to actual line bundles, rather than a comparison
between sheaf and module Picard groups. Its intended application is Conrad,
*Reductive group schemes* (2014), Proposition 6.2.11(2), pp.210–211.

Assume every `LineBundle S` is isomorphic to `LineBundle.trivial S`.
For an affine, flat, surjective morphism `p : X ⟶ S`, the theorem
`exists_unit_coboundary_of_lineBundlesTrivial` proves that every natural
multiplicative family of units on equal-composite pairs of maps to `X`
is a coboundary of an actual global unit on `X`. The base need not be affine.

The proof first applies the published effective unit-cocycle descent theorem
to produce a line bundle with trivialized pullback. The supplied Picard
hypothesis trivializes that actual line bundle. Comparing its pulled-back
trivialization with the descended one gives an automorphism of the structure
sheaf on `X`; the inverse of its scalar is the primitive. The change-of-frame
formula verifies the original all-test coboundary convention.

For a finite coordinate set `I`, `splitLineBundlePicardCochain` assembles these
unit primitives into an actual point of the split torus on the cover. Its
specification is the coboundary equation on every test scheme over `S`, and
`isTrivial_split_of_lineBundlesTrivial` records cocycle triviality. Finally,
when `S` is affine, `isTrivial_split_fppf_of_lineBundlesTrivial` extends this
to arbitrary single flat, surjective, locally finitely presented covers by
the published affine-refinement and original-cover descent construction.
No connectedness, reductivity or module-Picard hypothesis is required.
