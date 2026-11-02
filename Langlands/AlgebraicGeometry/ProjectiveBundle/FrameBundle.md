# A projective scheme from locally free sheaf frames

Let `M` be an actual structure-module sheaf on a scheme `S`, locally free
of the fixed finite rank `n + 1` in `IsLocallyFreeOfRank`. The construction
uses all opens carrying a genuine `LocalFrame M n U`, ordered by inclusion.
The given local generating bases supply such opens near every point.
Restricting a frame to a smaller open shows that these opens form a
topological basis. Their open subschemes therefore form a locally directed
open cover with an index type small in the scheme universe.

On each of these opens choose an actual frame of `M` and take its dual
frame. On an inclusion `U ≤ V`, use the coordinate change from the dual
frame on `U` to the dual frame on `V`, restricted to `U`. This is the
quotient convention: coordinates of a local functional are its values on
the original basis of `M`. The coordinate ring comparison `U.topIso`
transports the coefficients from sections of `S` on `U` to global
sections of `U.toScheme`.

Naturality of this comparison, coefficientwise restriction of frame
changes, and cancellation of coordinate equivalences prove the strict
identity and cocycle laws. Thus `frameCocycle` constructs the cocycle
required by the existing `CoordinateCocycle` gluing construction, using
only the locally free sheaf and its fixed-rank hypothesis.

`frameBundle` is the resulting actual scheme. Its structure morphism is
`FrameBundle.toBase`. The specified relative projective charts are open
immersions and cover the scheme, satisfy the displayed dual-frame
transition equations, and are Cartesian over their base opens.

This is derived internal infrastructure. The frame and coefficient
identities come from `LocalFrame`; the fixed-rank predicate supplies actual
local bases. Mathlib's `Scheme.restrictFunctorΓ` supplies naturality of
the canonical comparison of section rings. The existing
`CoordinateCocycle` construction supplies actual scheme gluing. No new
external source assertion is used.

The construction chooses local frames. Independence of such choices,
comparison with the functor of invertible quotients, a tautological
invertible sheaf and its universal property remain further work. This
file does not construct a representing ordinary moduli scheme.
