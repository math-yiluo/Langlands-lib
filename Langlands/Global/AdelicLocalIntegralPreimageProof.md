# Integral preimages under actual proper model morphisms: proof

The target is `Langlands.Global.AdelicLocalIntegralPreimageStatement` from its
unchanged statement module. This implements the local valuative ingredient in
the second paragraph of the proof of Conrad's Proposition 4.4, printed p.11.
The precise source and the derived generality are documented in the target's
paired Markdown.

`universallyClosed_ringPoint_preimage` proves the generic valuation-domain
equality directly on actual relative scheme points. Given an `L`-point `z` of
`X` whose image comes from an `R`-point `w` of `Y`, the equality of relative
points gives a commutative square of actual scheme morphisms by taking their
underlying morphisms. Mathlib's `UniversallyClosed.eq_valuativeCriterion`
supplies its existence part. The square uses the specified valuation domain
`R`, fraction field `L` and the actual spectrum map of `algebraMap R L`.

The resulting lift `Spec R → X` is a point over `Spec C`: its base equation
follows by composing the lift's equality over `Y` with the structure map of
`Y`, using the base equations for `f` and `w`. The other lift equality says its
coefficient extension is `z`, so it witnesses the required range membership.
Conversely, extending an integral point and then postcomposing with `f` is
the same as postcomposing first and then extending coefficients, by category
associativity. This proves the reverse range inclusion without any criterion
or injectivity argument. `valuationRingPointPreimage` packages the generic
statement.

For the curve and number-field clauses, the proof installs the original
outside-`S` integral-factor scalar action, and the field action given by
inclusion into the global field followed by completion. The scalar-tower
equation is reflexive, so the generic coefficient algebra homomorphism is
definitionally the one in the target. The completed integer rings are
Mathlib's actual valuation subrings, with the existing valuation-domain and
fraction-field instances. Properness supplies universal closedness. Applying
the generic theorem gives each arithmetic clause, and the final theorem
`adelicLocalIntegralPreimage` assembles the exact three-part target.

No topology, compactness, target finite type, separatedness, finite constants,
or nonempty-level assumption is used. This proves the local range equality
only; the global full-level comparison and full adelic properness remain
separate obligations.
