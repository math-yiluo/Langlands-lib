# Generic restriction laws for complex Weil representations

Worker 106 proves `Langlands.Weil.representationRestriction`, whose complete
closed type is `Langlands.Weil.RepresentationRestriction.{uG, uH, uV, uU}`.
The four universes remain independent. The theorem introduces exactly the
parameters and hypotheses of the published proposition, including arbitrary
topologies on the groups, continuity of the supplied homomorphism, and the
inertia inclusion. It adds no topological-group hypothesis.

## Implemented proof

For the homomorphism `φ : H →* G` and inertia subgroups `I` and `J`, the
inclusion `J ≤ I.comap φ` defines `f : J → I` by `f(j) = φ(j)`. The subtype
topologies and continuity of `φ` make `f` continuous. The proof establishes the
ten conjuncts in their stated order:

1. Continuity is preserved by composition with `φ`, using the target's usual
   module topology on the endomorphism space.
2. The new inertia kernel is definitionally the preimage of the old inertia
   kernel under `f`; continuous preimages of open sets are open.
3. The new inertia image is contained in the old inertia image, so it is finite
   when the old image is finite.
4. The whole image after precomposition is contained in the original image.
5. Triviality on `I` applies at `f(j)` to give triviality on `J`.
6. Product representations commute with precomposition by definitional equality.
7. Tensor products commute with precomposition by definitional equality.
8. The dual identity follows by extensionality and `φ(h⁻¹) = φ(h)⁻¹` in
   Mathlib's contragredient formula.
9. The determinant equality is definitional equality of its input operators.
10. An actual representation equivalence retains its linear equivalence, and its
    intertwining identity is evaluated at `φ(h)`. This works with `V` and `U`
    in independent universes.

The final example assigns the entire unapplied theorem constant to the target
with the four explicitly supplied universe levels. It does not specialize the
groups, carriers, or hypotheses.

## Provenance and scope

This is an internal, derived proof of the unchanged published statement in
[`RestrictionInduction`](RestrictionInduction.md). That statement's source map
locates the use of restriction in Tate, *Number theoretic background* (1979),
section 2.1, printed pages 9–10 (PDF pages 18–19), literature ID
`tate-1979-number-theoretic-background`. As explained there, these explicit
compatibilities are derived from composition and are not attributed verbatim
to Tate. The proof uses the existing Mathlib representations, product, tensor,
dual, determinant and representation equivalence. The continuous inertia
preimage argument also occurs in the published bundled theorem
`Langlands.FiniteRepresentation.hasOpenInertiaKernel_restrict`; here it is
applied directly to the target's unbundled action and subgroup inclusion.

Only this focused proof pair is added. The statement and its dependencies are
unchanged. No induction, reflection, Weil–Deligne, local arithmetic extension,
or local Langlands theorem is asserted.
