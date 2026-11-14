# Scalar transitions from exact vector lattices

Let `R` be a domain with fraction field `K`, and let `n > 0`. For units `s,t` in
`K`, the actual integral-point image of the vector model scaled by `s` is
contained in that of the model scaled by `t` if and only if there is `c : R`
with `algebraMap R K c * t = s`.

For the forward direction, the proof places the constant vector with all
coordinates equal to `s` in the `t` lattice. Its first coordinate supplies
`c`. The reverse direction multiplies each integral coordinate by `c`.
The exact-image formula used in both directions is the previously proved
formula for the actual integral-point map, rather than a replacement
definition of integral points.

The coefficient constructs an integral scalar map extending the generic
identity. When `R` is local, every such identity extension has a smooth,
connected and unipotent scheme-theoretic kernel on special fibres. The proof
uses generic rigidity and the previously calculated scalar kernel after
residue specialization. No valuation hypothesis or chosen uniformizer is
needed for these conclusions.

This is internal lattice algebra derived from `ScaledVectorPoints` and
`ScaledVector`, motivated by the additive transitions in Kaletha–Prasad,
*Bruhat–Tits theory: a new approach* (2023), Section C.2 and Fact C.2.1,
printed pp.697–698 / PDF pp.728–729, registered source
`kaletha-prasad-2023-bruhat-tits-new-approach`. It does not identify any supplied
root filtration with a principal vector lattice. The positive-dimension
hypothesis is essential to the stated coefficient criterion.
