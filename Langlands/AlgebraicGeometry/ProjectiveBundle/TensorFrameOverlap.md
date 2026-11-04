# Tensor-frame comparison on arbitrary overlaps

Let `M` and `N` be module sheaves on a scheme `S`. Suppose `e` is a genuine
rank `n+1` frame of `M` on `U` and `f` is such a frame on `V`, with actual
trivializations `t` of `N` on `U` and `s` of `N` on `V`. The two opens may
differ. Every comparison below is on any original open `W` contained in both.

`lineSection_eq_coordinate_smul` expands a section of `N` as its coordinate
times the coordinate-one section. Applying the other chart gives
`lineCoordinates_change_mul`.

`lineComparisonUnit t s W hWU hWV` is an actual unit of the section ring
`Gamma(S,W)`. Its value is the `s` coordinate of the `t` coordinate-one
section; its inverse is the `t` coordinate of the `s` coordinate-one section.
The two products equal one by applying the coordinate-change formula to those
basis sections. `lineCoordinates_change` states that changing from `t` to `s`
multiplies the original coordinate by this unit.

`tensor_overlap_dual_change_coefficient` computes every entry of the dual
transition from `e.tensor t` to `f.tensor s`. It is the original dual entry
multiplied by the reverse unit `lineComparisonUnit s t W hWV hWU`.
The proof uses the existing dual evaluation coefficient identity, expresses
the target tensor basis as a pure tensor using inverse contraction, then
contracts it in the source chart. Linearity gives the scalar formula.
Extensionality on standard basis coefficients upgrades this to the equality
of linear equivalences `tensor_overlap_dual_change`.

`tensor_overlap_projectiveChange` proves equality of the actual relative
projective scheme transitions for the tensor and source frames on `W`.
It transports the coefficient comparison to the global section ring of
`W.toScheme`, decomposes the action as the source transition followed by a
scalar action, and applies the established triviality of scalar-unit
projective actions. This is equality of scheme morphisms.

This module is derived from the existing frame, tensor restriction, section
transport and projective action APIs. It adds no local-freeness or invertibility
premise beyond the supplied genuine frames and line charts. Constructing a
global comparison by gluing, and the ordinary moduli representability theorem,
remain further obligations.
