# Finite-smooth parabolic-vanishing forms in the actual quotient L2

The input is the broader finite-smooth parabolic-vanishing form space of
`GroupSchemeCuspidalForms`, with full growth, whole-function compact and
center finiteness, the original carrier and every proper rational
parabolic with its constructed normalized quotient measure. It is not
identified with the literal GH smooth form space: the algebraic tensor
condition of GH (6.1) is not imposed or proved on that carrier. Its
injective continuous-function realization gives a finite adelic
subrepresentation by taking the actual range.

A continuous function on the existing positive rational quotient belongs
to `positiveCuspidalFormSubrepresentation` exactly when its actual
pullback equals one of those constructed original functions everywhere.
This imposes positive-center descent explicitly.
`positiveCuspidalFormL2Subrepresentation` also imposes genuine `MemLp`
at exponent two for the specified quotient measure. Neither condition
is automatic from the implemented form definition.

The resulting finite action restricts the existing positive right
action. The map to actual `Lp` is the existing continuous
`MemLp.toLp` realization restricted to this domain. It intertwines
finite translation, agrees almost everywhere with the continuous
representative and is injective for a quotient measure positive on
every nonempty open set. Its range is an algebraic subrepresentation.
A linear forgetting map into the published continuous-only parabolic
L2 construction uses exactly the canonical radical measures and gives
the identical actual L2 class. The canonical Haar specialization keeps
all original character restriction, finite-index, split-torus,
centrality and norm-one right-Haar-invariance hypotheses.

This is an internal restriction and compatibility construction. It
proves no literal GH tensor-space comparison, automatic square
integrability or positive-center descent, closedness/density, full
almost-everywhere cuspidal L2 equality, or greatest rational split-center
comparison. The original `hPD`, scalar commutator and measure premises
remain explicit.
