# Integral relation descent and positive basis extraction

This module proves the complete published proposition
`Langlands.VirtualRepresentation.IntegralDescentAndPositivityStatement`.
The closing theorem is
`Langlands.VirtualRepresentation.integralDescentAndPositivity`.
Its three independent universe parameters and all thirteen conjuncts are
preserved. The bases and the family of paired generators may be infinite or
empty. Worker 0 authored the proof terms. Worker 59 checked the full target,
audited the source and dependency correspondence, and prepared this paired
contribution for independent review.

## Objects and provenance

The construction is the actual finitely supported integer lattice from Worker
24's published `Langlands.VirtualRepresentation.Integral` module. Worker 30's
published `Langlands.VirtualRepresentation.DescentStatement` supplies the exact
target. Both published Lean/Markdown pairs remain unchanged. Their source and
application boundaries are described in the statement's Markdown: Henniart
2000, *Une preuve simple des conjectures de Langlands pour GL(n) sur un corps
p-adique*, sections 2.5-2.8, printed pages 445-448. These generic declarations
extract the elementary lattice argument; they are not literal statements of
Henniart's local representation theorem.

The registered original has literature ID `henniart-2000-simple-proof`,
registered file
`/home/taskhub/central-library/Henniart--Une preuve simple des conjectures de Langlands pour GL(n) sur un corps p-adique--2000.pdf`,
and SHA-256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
The statement's Markdown records an earlier retained path for the same file,
with the same SHA-256. Worker 59 read §§2.5–2.8 in that original. The passage proving Theorem 2.5
in §2.8, p.448, supplies the relation-descent and span-isometry argument;
Proposition 2.6(a), p.446, supplies degree preservation; the argument after
the corollary in §2.6, p.447, supplies the norm-one and degree-sign steps.
The explicit generic kernel, quotient, and basis-index uniqueness statements
are the published target's algebraic extraction of those arguments.

The proof below is a direct algebraic implementation for the concrete `Finsupp`
lattice and its integral coefficient pairing. It supplies no local
representation-class construction, Brauer spanning theorem, global comparison,
finite-stratum count, or local Langlands surjectivity result. Those are separate
application obligations. Natural-number degree weights can be zero except
where the published statement explicitly requires positive source weights.

## Implemented proof

`pairing_apply` expresses the pairing as a finite sum of coefficient products.
`coefficient_square_le_pairing` bounds every coefficient square by the
self-pairing. The self-pairing is nonnegative; if it is zero, every coordinate
is zero. This proves `integralPairingDefiniteness`.

For a norm-one vector, a nonzero coordinate exists and its square is at most
one. Integer arithmetic makes that coordinate one or minus one. Subtracting
or adding the corresponding basis generator has zero self-pairing, so
positive definiteness gives the signed basis vector itself. Evaluating a
coordinate proves uniqueness of the index (`signed_generator_index_unique`).
This is `integralNormOneSignedBasis`. For `integralPositiveDegreeBasis`, nonnegative
degree weights exclude the negative sign when the vector has positive degree.

The following steps implement descent to actual generated submodules.

- `pairing_extend_eq` extends equality of generator pairings in both variables
  using the free-basis extensionality theorem `integral_hom_ext`. `integralRelationDescent` applies positive definiteness
  to the resulting equal self-pairings and identifies the two kernels.
- `evaluateGenerators_surjective` identifies each generated span with the
  range of evaluation using `Finsupp.range_linearCombination`.
  `ker_evaluateGenerators` identifies its kernel with `relations`.
- `integralGeneratedEquivalence` uses `LinearMap.quotKerEquivOfSurjective`
  on both sides and `Submodule.quotEquivOfEq` for the equal kernels.
  Evaluation on a generator verifies the required images. The helper
  `generated_hom_ext` combines the free-basis extensionality theorem with
  surjective evaluation to prove uniqueness of the equivalence.
- `generated_map_evaluate` extends agreement on generators to all formal
  combinations. Pulling back along the surjective evaluation map and applying
  the two-variable pairing equality proves `integralGeneratedIsometry`.
  The analogous one-variable free-basis equality for degree proves
  `integralGeneratedDegree`.

`integralIsometryInjectivity` applies definiteness to a difference whose image
is zero. `integralIsometrySignedBasis` applies the norm-one theorem to every
source generator and chooses its target index and sign. If two different
source indices had the same target index, their orthogonal source pairings
would contradict the nonzero pairing of their signed images. Thus the index
map is injective. Finally, `integralIsometryPositiveBasis` uses preservation
of positive source degrees to select positive signs, uses injectivity of the
linear isometry to obtain injectivity on indices, and evaluates the degree
identity on each generator to recover equality of weights. Neither basis
result claims surjectivity of its index map.

All ten component theorems remain independently reusable under the namespace
`Langlands.VirtualRepresentation`. The closing theorem combines them, using
definiteness and the norm-one and positive-degree results on each side as
required by the thirteen-conjunct target. The generic helper
`extend_generator` selects the supplied integer module action explicitly;
no identification with a different scalar-action instance is assumed.

## Development validation and review boundary

Worker 59 checked the submitted source in the task's environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`) over Library commit
`30ceb5a0d89d8094c1663fc19f35416519b9a125`. The two imported project pairs,
`DescentStatement` and `Integral`, have the SHA-256 hashes named by the task
and are unchanged. The Lake build of this module reported no errors and no
warnings. The inspection of `integralDescentAndPositivity` reports a theorem
with level parameters `u`, `v`, `w` and the axioms `propext`,
`Classical.choice` and `Quot.sound` only. There are no project axioms or
proof holes.

A separate private file assigned each unapplied constant to its complete
statement type, without applying or reordering binders. All eleven
assignments elaborated. The closing assignment is:

```lean
universe u v w
example : ∀ (ι : Type u) (κ : Type v) (J : Type w),
    Langlands.VirtualRepresentation.IntegralDescentAndPositivityStatement ι κ J :=
  @Langlands.VirtualRepresentation.integralDescentAndPositivity
```

The other ten assign each component theorem, for example
`@integralRelationDescent`, to the corresponding component proposition over
the same independent universes. Worker 0's earlier development checks, made
with environment `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` over Library commit
`459d17160ca3aef5c5b4e8ba056125e56d9479a0` with the same imported pairs,
gave the same results.

These are development checks. Independent semantic review, the admission
Lake build and exact-target check, and Library publication remain required.
A consumer must use the published proof before treating it as an accepted
dependency.
