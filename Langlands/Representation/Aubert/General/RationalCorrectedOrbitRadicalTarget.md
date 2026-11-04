# Radical intersections on surviving corrected Aubert orbits

Author: Worker 76. The precise conditional orbit Jacquet inputs are due to
Workers 1255 and 969. Workers 164 and 6 contributed the residual-obligation
and ownership reconciliation. Worker 184 contributed the distinction from
the separate proper-target projection/image route.

`RationalCorrectedOrbitRadicalIntersectionStatement.{u}` in
`Langlands.Aubert.General.RationalPointFamily` is a proposition definition.
Its generic template is
`CorrectedFiltration.OrbitRadicalIntersectionTarget`. Neither definition
proves the assertion or asserts it for arbitrary subgroup families.

## Exact assertion

Fix a standard source index `I`, a valid position `j` of the existing
decreasing-length Weyl list, and an actual normalizer lift `m` of the inverse
of its entry `w`. Fix any standard index `K` for which the *whole* Levi
comparison holds:

```text
x ∈ M_I  ↔  m⁻¹ x m ∈ M_K.
```

For every removed-root set `s`, put `J = S \ s`. If `K ⊆ J` and `w` is
minimal in the entire Weyl double coset `W_J w W_I`, the conclusion is the
following pair of universally quantified assertions:

- `(S1)` If `x ∈ U_I` and `m⁻¹ x m ∈ P_J`, then `m⁻¹ x m ∈ U_K`.
- `(S2)` If `x ∈ M_J` and `x ∈ U_K`, then `m x m⁻¹ ∈ U_I`.

The conjunction groups exactly `hS1` and `hS2` of the published
`CorrectedFiltration.nonempty_orbitJacquetData_of_isLimitOfCompactSubgroups`,
specialized to the actual grade and inverse lift. The same `I`, `m`, `K` and
whole-Levi comparison are retained for every surviving `J`. No representation,
support-category membership, finite-length condition or nonzero-grade
condition is introduced.

With the existing order and radical inclusions, `(S1)` identifies
`U_I ∩ m P_J m⁻¹` with the already defined
`orbitUnipotentIntersection U_I U_K m = U_I ∩ m U_K m⁻¹`.
The existing `orbitKernelIntersection_iff` implements the corresponding
kernel-stabilizer identification. `(S2)` is the distinct assertion used by
`orbitTransition_descent_injective` to descend through the actual
coinvariant relations. Neither of these existing conditional lemmas proves
the corresponding rational containment.

## Rational premises and scope

The rational statement repeats the structural premises of
`RationalCorrectedGradedTransitionStatement`: an arbitrary nonarchimedean
local field, connected reductive group scheme, actual maximal split torus,
generic cocharacter, canonical `pointTopology`, and the displayed locally
compact, nonarchimedean and Hausdorff group instances. It retains the named
standard-cocharacter, standard-parabolic-order and standard-Levi-intersection
statements; relative roots; point normalizer and centralizer comparisons;
closed radicals and Levis; and the compact-limit condition for the radicals.
It also retains the root-length, positive-simple-reflection and actual
Levi-Weyl comparisons for the Coxeter system.

Shared premises unused by these subgroup expressions remain explicit with
underscored names. There is no additional intersection, support, projection,
integral or representation-theoretic hypothesis. The Weyl group is the
actual quotient by the full torus centralizer. Positive characteristic,
nonsplit and non-quasisplit groups, and the empty simple-root set are
included. Only the field universe `u` occurs in the rational proposition.

## Internal provenance and remaining work

This is an internal consumer prerequisite extracted directly from the
published `CorrectedOrbitJacquet` pair, section "Hypotheses", and its exact
`hS1`/`hS2` binders. It is not a transcription of a numbered literature
theorem. The public construction supplies the intended algebraic use of both
containments; this pair adds only their rational proposition target.

The actual rational containments still need proofs. A source-side twisted
Levi/radical intersection theorem alone does not identify the mixed
intersection in `(S1)`. A proof using an intrinsic root-intersection subset
must also identify that subset with the supplied `K` and transport all
membership assertions to the actual rational-point subgroups.

The separate proper-target geometric-lemma comparison needs projection
stability and a coefficient radical-image identification. Those statements
have different binders and are not replaced by this surviving whole-Levi
target. The prospective common-torus dynamic-limit route to them remains
separate, with its existing owners and proof obligations.

The squared intersection-modulus identity, fixed-order support topology,
quotient compactness, continuous projections, conditional orbit integral,
full-smooth exactness and terminal comparison remain separate obligations.
No existing target, import or external structural-input boundary is changed.
