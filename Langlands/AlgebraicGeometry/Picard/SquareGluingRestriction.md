# Restriction of actual Picard square gluing data

This internal construction restricts actual gluing data, including its specified
overlap isomorphism and every compatible pair of arrows. It uses the published
ordinary Picard pullback comparisons and Mathlib's comma-category functor.

`SquareGluingRestriction.pullback` takes two commuting scheme faces
`ι₁ ≫ g₁ = g₀ ≫ i₁` and `ι₂ ≫ g₂ = g₀ ≫ i₂`. The new legs are the ordinary
pullbacks along `g₁` and `g₂`. Its overlap first uses the canonical comparison on
the first face, then pulls back the original overlap along `g₀`, and finally
uses the inverse comparison on the second face. Naturality makes the pullback
of a compatible pair compatible.

`toOpen` specializes this functor to the exact inverse-image square constructed
in `InfinitesimalAffineOpenSquare`, using its left and right restrictions and
the actual inclusions of the three inverse-image opens.

This file constructs restriction of data. It does not assert compatibility
with a total-scheme comparison functor or prove global effectivity.
