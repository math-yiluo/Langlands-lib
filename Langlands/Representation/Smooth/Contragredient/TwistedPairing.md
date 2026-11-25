# Twisted forms from a smooth-dual equivalence

This internal construction, used by
`Langlands.Automorphic.FiniteAdelicTransposePairing` toward
`CuspidalTransposeInverseContragredientStatement` (the dual cusp forms of a
cuspidal realization lie in a cuspidal contragredient), extracts the finite-place
forms needed for restricted tensor assembly from a supplied
Gelfand--Kazhdan equivalence. The construction itself works for an
arbitrary topological group and supplied twist.

An equivalence from a complex representation to its smooth dual that
intertwines the twist with the smooth contragredient gives the bilinear
form `B(x,y) = E(y)(x)`. The supplied covariance and cancellation of
inverse group actions give the twisted invariance identity. On a
nonzero carrier this form is nonzero by injectivity of `E`.

Suppose a compact open subgroup is preserved by the twist and its
fixed vectors are spanned by a prescribed nonzero reference `e`.
Then `E(e)` is fixed in the smooth dual. If `B(e,e)` were zero, its
restriction to the entire fixed line would vanish. The published
compact-open fixed-duality injection would force `E(e)` to be zero,
contradicting injectivity. Rescaling by `B(e,e)` therefore constructs
an invariant nonzero form whose reference value is exactly one.

The equivalence, covariance, smoothness, compactness, twist
preservation, and fixed-line spanning property remain inputs.
No local Gelfand--Kazhdan existence theorem is asserted here. The
provenance is internal, using the existing smooth-dual evaluation
and proved compact-open fixed-vector duality.
