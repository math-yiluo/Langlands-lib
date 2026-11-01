# Composed induction in flattened coordinates on exact K0

Author: Worker 320.

`Langlands.Parabolic.normalizedFlattenedInductionK0` first changes from the
actual refined-subgroup Levi to the actual flattened product Levi using
`Geometric.flattenedLeviK0`, then applies the existing
`normalizedInductionK0` for `B.flatten S`.
`normalizedComposedInductionK0_eq_flattened` proves that this map equals
the existing exact K0 map of direct composed induction.

The parameters are an arbitrary prime `p` with `Fact p.Prime`, any actual
`F : PadicField.{uF} p` and compatible `T`, any rank `n`, block shape `B`,
and refinement `S`. The source is the full exact finite-length smooth complex
K0 of `refinedLevi F.Carrier B S`; the target is that of `GL_n(F)`.
The representation carriers are saturated at `max uF uV`, with independent
field and carrier universes. Rank zero and empty block families are included.
No admissibility, irreducibility or finite complex dimension is imposed.

The proof reduces equality of integer-linear maps to actual finite-length
object generators using `hom_ext_object`. For an actual refined-Levi object
`A`, pullback along `flattenedLeviEquivContinuous` gives the literal flattened
object `D`, and published preservation proves its finite group-algebra length.
Published preservation gives lengths of both the flattened-induced object `I`
and the direct composed-induced object `Q`. The direct composed, flattened
coordinate, and ordinary induction generator formulas rewrite the desired
identity to `[Q] = [I]`. The published
`composedFlattenedInduction` supplies an actual equivariant complex-linear
equivalence from `Q` to `I`. Isomorphism invariance of the exact Grothendieck
class concludes the proof.

This internal derivation reuses the published actual coordinate equivalence
and composed-to-flattened induction proof. It asserts no new
original-literature theorem. Both inductions retain the actual upper block
parabolics, positive half-modulus covariance, and right translation; the
existing comparison proves their normalizations agree. The K0 quotient
retains all actual short exact sequences, including nonsplit ones.
The result compares maps on every virtual class. It does not prove a Jacquet
comparison in flattened coordinates, a geometric-lemma sum, an Aubert identity,
or analytic segment classification.
