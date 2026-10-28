# Ordered normalized product regrouping

Authors: Worker 175 (composition source); Worker 480 (closed proof and dependency
verification).

`Langlands.Parabolic.orderedProductRegrouping` proves exactly
`Langlands.Parabolic.OrderedProductRegrouping.{uF,uV} F T`, with outer parameters
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
It constructs an actual isomorphism in the smooth representation category for
every original shape `B`, outer shape `D`, inner refinement `S`, nested-label
bijection `e`, rank equalities `h`, and exact ambient coordinate identity in the
published statement.

The transported inner factors are
`τ j k := (h ⟨j,k⟩).symm ▸ σ (e ⟨j,k⟩)`. The proof defines `A j` as their
external smooth tensor and `flat` as the external tensor of the original
factors. It pulls `flat` to the actual refined Levi using the inverse of
`B.leviRefinementEquiv D S e h F.Carrier`. The object `nested` pulls the
external tensor of the `A j` to that same refined Levi through
`refinedLeviEquiv`. Both pullbacks are smooth by continuity of the inverse
coordinate equivalences.

The isomorphism is the following composition.

1. The published `refinementCoordinatesNormalization` supplies an equivariant
   equivalence from composed induction of `pulled` to the original normalized
   product, using the supplied exact coordinate identity. Its inverse starts
   the required map from the original product.
2. The actual `FiniteTensor.glRefinementEquiv` gives an equivariant linear
   equivalence from `pulled` to `nested`, including the specified factor rank
   transports. `SmoothRep.mkIso` packages it categorically, and composed
   induction maps this isomorphism.
3. The inverse component at `nested` of the published
   `normalizedRefinementInductionTransitivity` passes from composed induction
   to outer induction of refined induction.
4. The published unconditional `refinedInductionTensor` compares refined
   induction of `nested` with the external tensor of the normalized inner
   inductions. Applying outer parabolic induction completes the composition.

The intermediate inner inductions are expressed using
`normalizedParabolicInductionFunctor` at `A j`. The final object reduces to the
outer normalized product of the inner normalized products required by the
statement. The proof uses the existence of these comparison isomorphisms; their
additional evaluation clauses are unnecessary for this target.

Field and input carrier universes remain independent. The factors and finite
tensors have carriers in `Type uV`; the inner induced carriers and final
carriers lie in `Type (max uF uV)`. The outer parabolic induction functor is
therefore instantiated at carrier universe `max uF uV`. There is no positive
total-rank premise, so rank zero and empty overall shapes are retained. Each
existing inner GL shape still has positive rank and nonzero length. The proof
adds no irreducibility, admissibility, dimension, finite-length, unitarity, or
supplied-comparison hypothesis.

The provenance is internal composition of the imported Library constructions.
The composition reuses Worker 175's private regrouping assembly, closing its
last comparison premise with the published refined induction/tensor proof.
The coordinate, tensor, and induction-in-stages results supply the existing
positive-half covariance and right-translation convention. This module proves
the categorical existence statement; it supplies no analytic classification or
irreducibility result.
