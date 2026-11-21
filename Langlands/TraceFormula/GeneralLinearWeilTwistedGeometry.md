# Geometry of rational sigma-elliptic twisted classes

The coordinate map `cyclicWeilAdelicMap` is the composite used in
`GeneralLinearWeilAdelicTwistStatement`, with domain
`(Res_{L/K} GL_n)(𝔸_K)` and target `GL_n(𝔸_L)`. Both propositions identify
the principal adelic point `r` with `δ ∈ GL_n(L)` by this map.

* `GeneralLinearWeilTwistedCompactQuotientStatement` asserts compactness of the
  left quotient of the actual norm-one twisted centralizer by its rational
  subgroup. `IsCompactTwistedCentralizerQuotient` expresses the same compactness
  for any subgroup `Γ` of the ambient topological group.
* `GeneralLinearWeilTwistedClosedOrbitStatement` asserts closedness of the
  range of `x ↦ x⁻¹ r θ(x)` in the actual norm-one group, with both the
  conjugator and the orbit point in that group.

The hypothesis `IsSigmaElliptic σ l δ` means that the cyclic norm of `δ`
is associated to a matrix over `K` with separable irreducible characteristic
polynomial over `K`. The norm algebra can split after extension to `L`.

These are the geometric inputs to the per-class finiteness and integrability
argument for the simple twisted trace formula. They use the centralizer
comparison from Arthur–Clozel, *Simple Algebras, Base Change, and the
Advanced Theory of the Trace Formula*, Chapter 1, Lemma 1.1, pp. 3–4,
and the setting of Getz–Hahn, *An Introduction to Automorphic Representations*
(2024), §18.5, pp. 487–488. The propositions isolate compactness and closedness
before passage to quotient measures and test functions.
