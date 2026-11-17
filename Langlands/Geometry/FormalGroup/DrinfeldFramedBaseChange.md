# Actual framed formal atlases over a varying Nilp base

This internal unit constructs coefficient extension of an actual height-zero
framed representative along a morphism of the given Nilp category. It derives
from the existing actual global-cover, quotient-naturality and rational-height
constructions; it makes no new original-source identification or
representability assertion.

`globalCoverOrderIsoOfCoverEq` retains the same actual global formal order
action on two supplied equal principal covers. Equality elimination gives the
actual identity formal isomorphism; no coordinate comparison is chosen as
extra input.

`SpecialAtlas.quotientFrameBaseChangeIso` compares extension of the original
fixed-frame source with the fixed frame on the quotient cover of the extended
target. The residue scalar map is the actual quotient map induced by the Nilp
morphism. The comparison first uses `globalCoverBaseAlongIso` to commute global
restriction and coefficient extension, then restricts the actual full-order
scalar-composition isomorphism, and finally transports to the equal target
cover supplied by the actual quotient naturality square. It retains complete
forward and inverse formal maps. It does not identify independent selected
original charts.

`DrinfeldFramedAtlas.baseChange` composes the stored residue map with that
induced quotient scalar map and extends the given height-certified target by
the actual Nilp scalar map. Its framing is the original full-order rational
quasi-isogeny extended along the quotient scalar map, transported through the
constructed source comparison and the inverse target quotient-naturality
comparison. Both rational maps and both inverse equations come from the actual
quasi-isogeny calculus.

The old all-test height-zero certificate survives scalar extension by
`HasConstantChartHeight.baseChangeAlong`. The full-order atlas isomorphism
transport theorem preserves this actual local kernel-rank height. The exact
underlying ambient tensor extension equation identifies the certificate with
the constructed framing's forward map. The two projection equations for the
residue map and actual extended target are definitional.

The parameters retain the local field `K`, finite-dimensional central division
algebra `D`, embedded field `L`, coefficient ring `R`, residue field `κ`, fixed
height-certified frame `Φ`, and Nilp objects in universes `{v,u}`. Original covers
may be infinite and the scalar/quotient maps may merge generators. No new frame,
representing object or universal object is assumed. Compatibility with actual
framed comparisons, descent to comparison classes, identity and composition of
framed extension, source-functor identification and group actions remain
further constructions.
