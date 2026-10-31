# Proof of the normalized geometric lemma for GL

Authors: Workers 164 and 194.

`Langlands.Geometric.padicGeometricLemma.{uF,uV}` proves exactly the
published proposition
`Langlands.Geometric.PadicGeometricLemmaTheorem.{uF,uV}`.
Its complete type has no extra premise. The field universe `uF` and
representation-carrier universe `uV` are independent.

The theorem retains every prime, actual finite p-adic extension, supplied
compatible topology, positive rank, and pair of block shapes. Its source is
the full smooth complex representation category of the source Levi, and its
target values lie in the complex representation category of the target Levi
with carrier universe `max uF uV`. There is no dimension, admissibility,
irreducibility, or length restriction.

The proof composes published results as follows.

1. Install the supplied field topology, valuative relation, local-field
   structure and Hausdorff certificate, together with the nonarchimedean,
   locally compact, Hausdorff and sigma-compact structures on the actual
   general linear group. The sigma-compact certificate is imported from
   `CountabilityProof`.
2. Specialize `padicParabolicBruhat` to the two block shapes. Its surjectivity
   makes the actual parabolic double-coset quotient finite because the
   minimal permutation representatives form a finite type.
3. Apply `closedSubgroupOrbitOrdering_of_finiteOrbitOrdering` to the proved
   `Langlands.Topology.finiteOrbitOrdering`. Both actual block parabolics
   are closed in the supplied topology. The result is a finite, disjoint
   cover by their actual double-coset orbits with open initial unions.
4. Choose source and target refinements separately from
   `padicStandardIntersectionsTheorem`. Their witnesses give all three
   parabolic, Levi and unipotent subgroup equalities, including the inverse
   permutation on the target side. These conjunctions are precisely the
   `IsIntersectionRefinement` predicates used by the geometric-lemma target.
5. Apply the published `geometricLemma_of_orderedCosets` to this ordering,
   the Bruhat bijection, and the chosen refinements. That assembly uses
   `minimalPermutationOrdering` to enumerate every minimal representative
   exactly once and to replace the ordering by its permutation matrices
   without changing the ordered orbit sets.
6. Discharge the assembly's remaining comparison premise by specializing
   `padicParabolicSupportGradedTheorem` to that enumeration, replacement
   ordering and both refinement families.

The witnessing filtration is the specified
`parabolicJacquetSupportFiltration` for the replacement ordering: its
natural subfunctors start at zero and end at the actual
`jacquetInductionFunctor`. The comparison supplies natural isomorphisms from
its actual consecutive quotient functors to the literal
`geometricPieceFunctor` list. The conditional assembly inserts this
filtration into `IsGluedFrom` with the identity permutation of that list.
Thus the construction chooses one filtration for the whole source category,
with compatibility for every intertwiner. It asserts a filtration and does
not assert a splitting.

The orbit convention remains `P_B * w⁻¹ * P_C`. The geometric piece first
takes normalized inner Jacquet, transports by inverse matrix conjugation,
and then takes normalized inner induction. The published graded comparison
has already canceled the intermediate normalization factors: induction
uses the positive half modulus and Jacquet the inverse positive half.
There is no residual character in the conclusion.

This is an internal final assembly of the published concrete Bruhat,
standard-intersection, orbit-ordering, support-filtration and normalized
graded-comparison results. Worker 194 supplied the conditional assembly and
the universal-input draft; Worker 164 supplied the concrete ordering and
the closing specialization. No private draft is imported by this module.
The statement's Lean/Markdown pair and every imported pair are unchanged.

The original mathematical source is Bernstein and Zelevinsky, *Induced
representations of reductive p-adic groups I* (1977), registered as
`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Sections 2.11–2.12 (printed p.448, PDF p.9) give the intersection and
functorial gluing statements; sections 5.1–5.4 (pp.459–461) describe orbit
ordering and the support filtration; sections 5.5–5.17 (pp.461–467) prove
the local comparison; sections 6.3–6.4 (pp.468–469) specialize the
intersections and remove the extra normalization character. The Lean proof
uses the published results implementing these ingredients. Its scope is
the stated positive-rank p-adic GL specialization.
