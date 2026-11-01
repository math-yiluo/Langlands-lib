# Smooth induction across a topological group equivalence

This internal construction extends the published same-group precomposition
construction in `Induction.InverseTranspose` to two possibly different ambient
groups. It is derived directly from `Induction.Definitions`; it introduces no
additional literature assertion or representation-theoretic hypothesis.

Let `θ : H ≃ₜ* G` identify the topological groups and `e : Q ≃* P` identify
subgroups in a way compatible with their inclusions and `θ`. Assume that the two
inducing actions on the same module satisfy `σ (e q) = τ q`.
`precomposeSmoothInducedGroupEquiv` is an actual representation equivalence from
smooth induction from `P`, with its ambient action pulled back along `θ`, to
smooth induction from `Q`.

The forward map is `f ↦ (x ↦ f (θ x))`. Its left covariance follows from the
subgroup and inducing-action equalities. If `K` is a uniform open right
stabilizer of `f`, the inverse image open subgroup of `K` under `θ` stabilizes
the image function. The inverse is precomposition with `θ.symm`, using
`e.symm`. Their composites are the identity by the two inverse identities for
`θ`. Both maps are linear by pointwise operations, and the forward map
intertwines right translation because `θ (x * h) = θ x * θ h`.
The two exported evaluation lemmas give these forward and inverse formulas.

The scalar ring, both group universes, and the module universe are independent.
The construction requires no finite-dimensionality, finite length, admissibility,
or irreducibility. It concerns the actual smooth function spaces and their
uniform open stabilizers.
