# Actual pullback charts and local determinant transport

This internal construction composes the published actual chart pullback and local
sheaf-isomorphism transport. It is derived from `LocalChartDeterminantPullback`,
`LocalSectionIso` and `ModuleDualPullbackLocalFree`; no separate original-source
translation is asserted.

For `f : X ⟶ Y`, a module sheaf `M` on `Y`, an open `U` and a finite free
chart `e` of `M.over U`, let `h` be an actual local sheaf isomorphism from the
restriction of `f`'s pullback of `M` to `N.over (f ⁻¹ᵁ U)`.
`chartFreePullbackTransportIso f e h` is the finite free chart on `N` obtained
by composing `chartFreePullbackIso f U e` with `h`. Its construction uses the
actual scheme-module pullback, not a supplied target basis.

If a local endomorphism `a` and a target endomorphism `b` satisfy
`localHomPullback f U a ≫ h.hom = h.hom ≫ b`, their matrices in the source
and constructed target charts agree after mapping source coefficients by
`f.app V.left`, for every `V : Over U`. The target smaller open is the inverse
image of `V.left` inside the inverse image of `U`. The proof first applies
local isomorphism transport and then the actual chart pullback matrix identity.
For a finite family with the same intertwining isomorphism, the corresponding
universal determinant polynomials and every monomial coefficient obey the same
formula. Existing trivialization independence extends the polynomial equation
to any finite target chart on the same inverse-image chart open, including a
different finite basis index type.

`localHomPullback_over` identifies local pullback of a restricted global map
with the restriction of its actual global pullback. It follows from the
published local-pullback naturality and identity laws. Applying the over
functor to a global intertwining equation therefore supplies the precise local
intertwining equation used above (`localHomPullback_over_intertwine`).

Schemes, modules and finite basis indices are in universe `u`; the finite
endomorphism family may use an independent universe `v`. The rings of sections
are arbitrary commutative rings, including rings with nilpotents. There is no
flatness or characteristic hypothesis. The local isomorphism and its
intertwining equation are explicit inputs. The module does not construct a
canonical Lie comparison or prove its naturality, and it does not assert the
global Harris determinant condition on an arbitrary target chart open.
