# Final-topology comparison for actual filtered scheme points

This is a derived target for Brian Conrad, *Weil and Grothendieck approaches
to adelic points* (31 December 2011), printed pp. 5–6, Theorem 3.4(1) and
Remark 3.5, and printed p. 9, section 4, first three paragraphs. The registered
source is `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The underlying constructions are in `FilteredRingPoints` and
`FilteredRingPointTopology`; the separate point-bijection and open-stage
targets are in `FilteredRingPointStatement` and
`FilteredRingPointOpenStatement`.

`FilteredRingPointTopologicalComparison` quantifies over a commutative ring
R, a small filtered category J, a diagram F of commutative R-algebras, an
algebra cocone c with an actual `IsColimit` witness, and an arbitrary scheme
X over Spec R whose structure morphism is locally of finite presentation.
These objects share one arbitrary universe. Every stage has an independently
specified topology τ i on its actual relative scheme points
`RingPoint R X (F.obj i)`. No topology on the value rings is assumed.

The first conclusion identifies the actual type-colimit of stage points,
with its final topology, with the actual points of X over c.pt, with the
independently constructed cocone final topology. The homeomorphism's
underlying function must be the canonical `ringPointColimitMap`, pointwise.
Bijectivity is a conclusion of local finite presentation and the algebra
colimit, rather than a premise. No continuity or openness assumption on
the transition maps is used for this conclusion.

The remaining conclusions assume that every actual point transition is
both continuous and open:

- Every actual change-of-algebra map from a stage to c.pt-valued points
  is open, for the stated stage and cocone topologies.
- If every stage is locally compact, the cocone-point space is locally
  compact. No injectivity or Hausdorff hypothesis is imposed here.
- If a countable set S of stage indices has images covering every actual
  c.pt-valued point, and those selected stages are second countable, the
  cocone-point space is second countable. The coverage premise explicitly
  quantifies actual representatives from the selected stages. In particular,
  a countable cofinal family of stages has this coverage property by
  finite-presentation factorization and compatibility of the cocone maps.
- If all point transitions are additionally injective, every stage map
  to actual c.pt-valued points is an open embedding. Under this injectivity
  premise, Hausdorffness of every stage implies Hausdorffness of the
  cocone-point space.

The generic hypotheses are an internal extension of Conrad's application.
The finite-presentation comparison is the fixed-model part of (3.5.1),
with local finite presentation sufficient for the existing general scheme
limit theorem. The topology comparison then uses the two independently
defined final topologies and this actual bijection. Openness transports
from the actual point colimit. Local compactness follows by mapping a
compact neighborhood from a representative's stage, using continuity and
openness. Second countability follows from the open continuous surjection
from the disjoint union of the selected countably many stages. These
arguments also justify allowing noninjective transitions in these two
conclusions. For Hausdorffness, filteredness puts any two points in a
common stage; an open embedding carries disjoint neighborhoods in that
Hausdorff stage to disjoint open neighborhoods in the whole space.
Thus no assertion that Hausdorffness is local for arbitrary open covers
is being used.

This file only states the proposition. It does not supply its proof.
Conrad's arithmetic application still requires actual local and adelic
rings, the global product stage topologies of Theorem 3.6 (including for
nonaffine schemes), their transition properties, the stage finiteness and
separation properties, and a countable covering family. Varying-model
comparisons, model independence, compatibility with fiber products and
the remaining whole-paper assertions are not conclusions of this target.
