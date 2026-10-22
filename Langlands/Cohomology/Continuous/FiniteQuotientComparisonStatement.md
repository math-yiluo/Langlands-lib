# Exact finite-quotient comparison proposition

Author: Worker 22. This pair states the exact isomorphism assertion; its
proof is a separate contribution. The imported definition is published at
`1058c134c0d2fb45ec96d08ea2956983aaac1d80`; its prerequisite cochain
comparison proof is published at `22b4f024e0d4218752e970d09329d1799f6d81d1`.

`Langlands.Continuous.FiniteQuotientComparisonIsIso` is a `Prop`-valued
definition. For every commutative coefficient ring `k` equipped with a topology,
every compact locally compact topological group `G`, every jointly
continuous discrete module `A : DiscreteModule k G`, and every natural
degree `q`, it asserts
`IsIso (Langlands.Continuous.finiteQuotientComparison A q)`.

The map is the named canonical map defined in
`Langlands.Cohomology.Continuous.FiniteQuotientComparison`. Its source is
the actual categorical colimit of the actual groups `H^q(G/N,A^N)`, with
the genuine inflation transition maps, over open normal subgroups ordered
by reverse inclusion. Compactness makes each quotient finite.
Its target is the underlying module of Mathlib's actual continuous
cohomology of the same action. The proposition asserts invertibility
of this specific map, rather than existence of an unrelated abstract
isomorphism.

The arbitrary common universe `u` contains the ring, group and coefficient
carrier. Thus the statement applies over `ULift.{u} ℤ` with a discrete
additive coefficient module in `Type u`. It requires neither a finite-quotient
comparison assumption nor an assumption about a cochain colimit, homology
exactness, or an unspecified equivalence.

Compact Hausdorff profinite groups satisfy the topological hypotheses.
The somewhat more general compact locally compact formulation is used
because these are exactly the hypotheses needed for finite cochain descent
and joint evaluation of the nested continuous model. No separation or
total-disconnectedness assumption is added.

The source is Serre, *Local Fields*, Greenberg translation, Springer (1979),
X Section 3, printed pages 154–155 / PDF pages 160–161. Serre's direct-limit
and continuous-cochain description is implemented for the specific nested
model in pinned Mathlib; that model and the passage to homology must be
handled in the separate proof. Literature ID `serre-1979-local-fields`,
PDF SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

Environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, version 1:
Lean 4.34.0 (`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`);
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
This statement does not assert corestriction or its laws.
