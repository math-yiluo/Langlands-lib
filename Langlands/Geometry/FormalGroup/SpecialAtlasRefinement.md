# Refinement of special formal division-order atlases

This derived unit restricts a supplied special formal division-order atlas
to an actual finer principal-open cover. It retains specialness, preserves
the supplied height certificates in the forward direction, and constructs
the natural equivalence on complete compatible families.

## Source and hypotheses

Drinfeld, *Coverings of p-adic symmetric regions* (1976), printed p.109
(PDF page 3), permits formal groups glued over localizations immediately
before section 2. Section 2 A defines special formal division-order modules
using dimension d and distinct geometric tangent characters, and imposes
height d² in the moduli problem. The registered source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The refinement construction here is derived infrastructure for this
local-coordinate convention, rather than a separate theorem of the source.

The parameters are a nonarchimedean local field K, a finite-dimensional
central division K-algebra D, an embedded field L, and a commutative
integer-ring algebra R. Put d = `CentralSimple.reducedDegree K D`.
The supplied `SpecialAtlas` has coordinate type `Fin d`, its actual
division-order action, the explicit unramified full-degree subfield
certificate, and geometric tangent-character certificates. These are the
existing hypotheses of `SpecialAtlas`; this unit proves neither subfield
existence nor specialization to Hasse invariant 1/d.

The supplied `q : BasicAtlas.CoverRefinement X.atlas` includes an actual
finer cover, its covering equation, the chosen original chart for each
finer chart, and the principal-open containment witnesses. Covers may be
infinite. Test algebras have the universe v of R and complete-family point
modules have universe v + 1.

## Formal construction and preservation

`SpecialAtlas.refine` uses exactly `q.atlas` and
`q.orderAction X.order`. The embedded unramified field certificate is
unchanged. Each tangent certificate is mapped from `q.source b` along the
actual localization coefficient map `q.chartCoefficient b`.

`refine_height` assumes `X.HasHeightSquared pi`: irreducibility of pi,
nilpotence of its actual image in R, and actual
`HasPiHeight pi (Nat.card` of the residue field`) (d^2)` on every original
chart. The first two conditions remain the same. Each chart certificate
maps along `q.chartCoefficient` using the existing scalar-kernel
coefficient-extension theorem. No height reflection or descent theorem is
asserted.

## Actual points and naturality

`refinementChartEquiv` evaluates the actual formal order-linear chart
comparison constructed in `AtlasOrderRefinement`. Both directions
preserve the underlying nilpotent coordinate tuple, as the two formula
lemmas state.

`refinementPointEquiv` specializes the full-family division-order-linear
equivalence. Its forward map restricts the original family to
`q.restrictTest t` at each finer test t. Its inverse has value
`q.gluedValue y t` at each original test t: this is the previously
constructed gluing of matching localized tuples, not an arbitrary
point-set inverse.

`refinementPointEquiv_natural` gives the coefficient-algebra naturality
equation. `refinementPointFunctorIso` packages the same constructed maps
as a natural isomorphism of module functors, and
`refinementNilpPointFunctorIso` restricts it to tests where the image of a
specified base element is nilpotent. No framing, quotient moduli functor
or representability result is claimed.
