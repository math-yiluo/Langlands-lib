# The integral projection from a ring pullback

This internal algebraic construction supplies a property of the affine
ring pullback used in integral scheme pinching. Let `f : R →+* T` be
surjective and let `g : S →+* T` be integral, for arbitrary commutative
rings in independent universes. The actual compatible-pair subring
`f.pullback g` projects integrally to `R`.

`isIntegral_pullbackFst_of_surjective` proves this directly by monic
polynomials. For `r : R`, choose a monic polynomial `p` over `S` which
vanishes at `f r` under `g`. Surjectivity of `f` makes the second
pullback projection surjective, so Mathlib's polynomial lifting theorem
gives a monic lift `q` over the pullback ring. The polynomial `q * X`
still vanishes after applying `f`. Its value at `r` therefore lies in the
kernel of `f` and defines a pullback element `a` with second coordinate
zero. Subtracting `C a` makes `q * X - C a` vanish at `r` exactly. Its
positive degree keeps it monic.

Multiplication by `X` ensures positive degree even if the original
polynomial has degree zero, including when `S` is the zero ring. If `R`
is the zero ring the integrality assertion is immediate; otherwise the
first projection gives a nontrivial pullback ring, so the positive-degree
calculation applies. No domain, reducedness, finite-generation or
nonzero-ring assumption is added.

`integralPullbackProjection` is the first projection bundled with this
proved integrality property. This unit supplies the algebraic property;
it does not assert a scheme pushout or any global gluing result.
