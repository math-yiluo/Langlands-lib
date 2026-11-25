# Full-order atlas isomorphism transport of actual local rational heights

This module transports actual full-order rational atlas maps and their
local kernel-rank heights by specified source and target formal isomorphisms.
It derives from the existing rational composition calculus, actual chart
isomorphisms and `RationalHeightIso`; no new literature assertion is made.

`OrderAction.RationalHom.isoTransport a b` is the linear map sending `f` to
`b.hom ∘ f ∘ a.inv`, with the integral maps rationalized inside the existing
full-order rational centralizers. It maps from the original source and target
to the specified new source and target. The cover equality follows the reverse
source-cover equality, the original equality, and the target-cover equality.
Thus different coordinate types and separately presented equal covers are
allowed. Linearity follows from the existing bilinearity of composition.

`RationalHom.isoTransport_height` evaluates the actual composition on each new
target test chart. Its original target chart is obtained by the target-cover
equality, and its new source chart by the inverse source-cover equality.
The supplied actual atlas isomorphisms yield actual formal-module chart
isomorphisms. The old all-test height certificate applies to the original
chart; `ofGlobal_isoTransport` retains its local numerator and denominator
kernel ranks. The exact tensor coordinate-change equation and chart-composition
equations identify that section with precisely the transported atlas tensor.
No equality of formal maps is inferred from their point evaluations.

`QuasiIsogeny.isoTransport` composes the inverse of the rationalized source
isomorphism, the given actual quasi-isogeny and the rationalized target
isomorphism. It retains both actual rational maps and their inverse equations.
Its forward map is definitionally the preceding tensor transport. The height
theorem applies the proved tensor result and certifies the original signed
constant height of that forward map; it makes no height assertion about the
inverse without an additional hypothesis.

The parameters are commutative rings `O` and `R`, a field `F` over `O`, an
acting ring `D` over `O`, finite coordinate types and actual atlas order actions
with the specified cover equalities. `R`, `F` and tests share universe `v`;
`O` and `D` may be in separate universes. The quasi-isogeny construction also
retains the existing domain and fraction-field hypotheses on `O` and `F`.
Covers need not be finite. Framed varying-base extension is constructed in
`DrinfeldFramedBaseChange`; its source-frame comparison remains separate.
