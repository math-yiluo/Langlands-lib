# Inner representatives of the actual special-linear Galois discrepancy

Author: Worker 239.

This internal unit works with the actual `LocalGroupIso E` from the special
linear group over a field-extension cover to a group scheme over a field `K`.
The algebraic lemmas need only that the cover field `L` is a `K`-algebra; no
finiteness, Galois, or classification hypothesis is used.

`HasInnerDiscrepancy E σ X` states that, on every test scheme and at every
point of its extension-field cover, the discrepancy of `E` for `σ` is
conjugation by the coefficient image of the actual matrix `X` in `GL(L)`.
The identity is represented by the identity matrix. Two such inner
discrepancies compose with representative `X * map σ Y`, by the published
composition formula for discrepancies and pullback formula for coefficients.

`baseCoefficientsEquiv` is the canonical equivalence from `L` to the global
sections of its spectrum. It identifies the coefficients of the identity
cover point. Evaluation on this test and injectivity of the equivalence show
that two all-test representatives of the same discrepancy induce equal
conjugations on `SL(L)`. `projective_cocycle` applies this comparison to the
product formula, for any subgroup of the field automorphisms and any supplied
family of inner representatives.

`subgroupRingAction` records the actual ring action of the automorphism subgroup.
Dividing the representatives by their eigenvalues on a supplied common coordinate
line preserves their all-test discrepancy formula. `normalized_identity` and
`normalized_cocycle` give the identity and composition laws for that normalized
family, by the scalar uniqueness and normalization unit. These are suitable for
matrix Hilbert 90, once the line-preservation hypotheses are available.

Finally, if the local coordinate matrix of a supplied point of `G` is
independent of the cover point, every discrepancy fixes it. An inner
representative therefore commutes with that matrix after the coefficient
map. In particular these lemmas can be applied to the diagonal split-torus
coordinates in the type A presentation, once that coordinate formula is
supplied.

The proofs unfold the actual discrepancy and use inverse equivalences,
coefficient maps and group cancellation. No inner representatives, invariant
coordinate line, or Hermitian presentation are asserted
to exist.
