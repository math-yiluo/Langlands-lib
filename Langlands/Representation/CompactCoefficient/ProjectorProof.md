# Natural compact-isotypic projectors: proof

The theorem `Langlands.compactCoefficientProjector` proves the published
proposition `Langlands.CompactCoefficientProjectorStatement.{uG, uV, uW} G μ`
of `Langlands.Representation.CompactCoefficient.ProjectorStatement`. It takes
exactly the binders of that statement:

```lean
(G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
[T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
[SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
(μ : Measure G) [Measure.IsHaarMeasure μ] [Measure.Regular μ]
[Measure.IsMulRightInvariant μ]
```

The group universe `uG`, the representative universe `uV` and the ambient
universe `uW` stay independent; the theorem has exactly the three universe
parameters `uG uV uW`. Nothing is assumed about the ambient smooth
representations: no admissibility, irreducibility, finite length, finite
dimension, compact coefficients, supplied projectors or complementarity.
The statement Lean/Markdown pair and its imports are unchanged.

## The projector family

The family is
`CompactCoefficientClass.isotypicProjectorFamilyOfIsCompl h`, from the
published module `OrthogonalProjectorFamily`. For a class `c` and a smooth
representation `A` it is the published `isotypicProjectorOfIsCompl c (h c A)`,
the equivariant projection of `A` onto the intrinsic
`isotypicSubrepresentation c A` along the intrinsic
`annihilatorSubrepresentation c A` (module `ConditionalProjection`). Here `h`
is the proof that these two subspaces are complementary for every class
`c : CompactCoefficientClass.{uG, uV} G` and every
`A : SmoothRep.{0, uG, uW} ℂ G`. The proof constructs `h`; it is not a
hypothesis of the theorem.

The index `c` is the actual quotient `CompactCoefficientClass` and the
subspaces are the unchanged published intrinsic definitions: the supremum of
the ranges of all intertwiners from representatives of `c` into `A`, and the
infimum of the kernels of all intertwiners from `A` to representatives of `c`.
No subspace is defined through the projector.

## Complementarity

The proof first derives compact-open cofinality,
`hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K`.
For an open subgroup `K`, the published
`Hecke.TestFunction.commonCompactOpenBiInvariance G ∅ K`, applied to the empty
family of test functions, gives a compact open subgroup `L ≤ K`. This uses that
`G` is a Hausdorff, locally compact, totally disconnected topological group.

Then `h` is the published
`CompactSplitting.isCompl_isotypicSubrepresentation_annihilatorSubrepresentation μ hcof`
(module `AdmissibleComplement`). That theorem uses only the left Haar measure
`μ` and `hcof`. Its proof makes each irreducible compact-coefficient
representative admissible, via finite-dimensionality of compact-open fixed
vectors, and then proves disjointness with equivariant retractions and
exhaustion with equivariant sections. That module records the full argument.

## The six conclusions

Write `P c A` for the family above.

1. **Idempotence.** The published `isotypicProjectorOfIsCompl_idempotent`
   gives `IsIdempotentElem (P c A).toLinearMap`. Its equation
   `p * p = p` in the endomorphism ring is the equality of underlying linear
   maps of `(P c A).comp (P c A)` and `P c A`, and
   `Representation.IntertwiningMap.ext` turns it into the stated equality of
   intertwiners.
2. **Intrinsic range and kernel.** These are exactly the published simp
   lemmas `isotypicProjectorOfIsCompl_range` and
   `isotypicProjectorOfIsCompl_ker`: `(P c A).range` is
   `isotypicSubrepresentation c A` and `(P c A).ker` is
   `annihilatorSubrepresentation c A`, as equalities of subrepresentations.
3. **Naturality.** For `A B` in the ambient universe and an intertwiner
   `f : A → B`, the published `isotypicProjectorOfIsCompl_natural c (h c A)
   (h c B) f v` gives `f (P c A v) = P c B (f v)` for every vector `v`.
   Extensionality gives `f.comp (P c A) = (P c B).comp f`. That lemma rests on
   the published facts that intertwiners map intrinsic isotypic parts into
   isotypic parts and annihilators into annihilators.
4. **Orthogonality.** For `c ≠ d`, the published
   `isotypicProjectorFamilyOfIsCompl_orthogonal h` applied to `d ≠ c` gives
   `(P c A).comp (P d A) = 0`. It holds because the range of `P d A`, which is
   the isotypic part of `d`, lies in the annihilator of `c`, the kernel of
   `P c A`: a map between representatives of distinct classes is zero.
5. **Compact coefficients of the range.** The published
   `hasCompactSmoothDualCoefficients_subrepresentation_of_le hcof A` (module
   `TotalCompactness`) gives compact smooth-dual coefficients for the actual
   restricted action on a subrepresentation, provided each of its vectors has
   compactly supported coefficients against every smooth functional of the
   ambient representation. It extends smooth functionals of the subspace to
   smooth functionals of `A`. The proof rewrites `(P c A).range` as
   `isotypicSubrepresentation c A`. That subspace lies in the total intrinsic
   isotypic part (`isotypicSubrepresentation_le_totalIsotypicSubrepresentation`).
   The total part consists of such vectors
   (`totalIsotypicSubrepresentation_le_compactCoefficientVectors`), because
   every vector in the range of an intertwiner from a compact-coefficient
   representation has compactly supported coefficients.
6. **Fixed-vector vanishing.** For a compact open `K` with
   `¬ HasFixedVector K.toSubgroup c` and a `K`-fixed vector `v` of `A`, the
   published `isotypicProjectorFamilyOfIsCompl_vanishes_on_fixedVectors h c A
   K.toSubgroup hc hv` gives `P c A v = 0`. The vector `v` lies in the
   annihilator of `c`, the kernel of `P c A`, because every intertwiner to a
   representative sends it to a fixed vector of that representative, and these
   fixed spaces are zero. Compactness of `K` is not used.

## Hypotheses not used

The statement's hypotheses `SigmaCompactSpace G`, `Measure.Regular μ` and
`Measure.IsMulRightInvariant μ` are accepted but not used: the proof needs only
a Hausdorff, locally compact, totally disconnected topological group with its
Borel structure and a left Haar measure. In particular unimodularity is not
used. The proof does not use semisimplicity, fixed-level finiteness of classes,
the final Levi decomposition, or any unproved Library statement.

## Relation to the source

The statement records Bernstein–Zelevinsky (1976), §§2.42–2.44. The Lean proof
does not follow the source route through projector distributions (§2.42) and
their natural idempotents (§2.43). It obtains complementarity of the intrinsic
subspaces directly and defines the projector by that splitting. By the
published `equivariantProjection_unique`, an equivariant idempotent with the
intrinsic range and kernel equals this projection, so conclusions 1 and 2
already determine the family. This uniqueness is not part of the theorem.

## Dependencies

- `Langlands.Representation.CompactCoefficient.ProjectorStatement` (target).
- `Langlands.Representation.CompactCoefficient.OrthogonalProjectorFamily` and,
  through it, `ConditionalProjection`: the projector family and its laws.
- `Langlands.Representation.CompactCoefficient.AdmissibleComplement`:
  complementarity.
- `Langlands.Representation.CompactCoefficient.TotalCompactness`: compact
  coefficients of subrepresentations.
- `Langlands.Representation.Hecke.CommonInvarianceProof`: compact open
  subgroups inside open subgroups.

The axioms used are `propext`, `Classical.choice` and `Quot.sound`. The
compilation environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`).

Authored by Worker 249.
