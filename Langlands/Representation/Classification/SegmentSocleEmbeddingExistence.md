# Nonempty actual segment-socle embedding data

Author: Worker 494.

This internal construction proves that every irreducible smooth complex
representation of `GL_n(F)` embeds into the actual normalized product of
some actual segment socles. The field universe `uF` and carrier parameter
`uV` are independent. The irreducible representation, cuspidal factors and
segment data all have the saturated carrier universe `max uF uV`.
The rank can be any natural number, including zero.

`T.exists_segmentSocleEmbedding π hπ` produces an actual fixed-rank
`SegmentProductDatum` with `HasSocleEmbedding π`. Thus every block is a
strong socle of its individual segment induction, and an actual injective
intertwiner embeds `π` into the full normalized product. This does not
assert that the segments are precedence ordered or that the full product
has a unique irreducible subobject. The latter are separate inputs to
multisegment socle exhaustion.

`T.socleEmbeddingDatum π hπ` chooses such a datum by classical choice;
`socleEmbeddingDatum_hasSocleEmbedding` records the chosen datum's property.
The construction makes no canonical choice.

## Implemented proof

At rank zero, the proof uses exactly `SegmentProductDatum.empty`. It takes
the actual injection from
`Classification.emptySegmentProduct_isZelevinskySocle` and the vacuous
individual segment-socle property. The chosen datum definition makes no
additional assertion about its numerical presentation.

At positive rank, `Langlands.glSupercuspidalEmbedding` produces a finite
ordered family of actual cuspidal data and a genuine cuspidal-product
embedding. Its factor universe is specialized to `max uF uV`; hence its
output representation universe `max uF (max uF uV)` is the required
`max uF uV`. The theorem
`IsCuspidalSubrepresentation.exists_segmentSocleProduct` from
[SingletonSegmentSocle](SingletonSegmentSocle.md) replaces each cuspidal
factor by its one-member segment, retaining its actual representative.
The explicit normalized-product equivalence transports the original
injective intertwiner. No permutation or ordering step occurs.

## Independence audit

The positive-rank input is the proved theorem
`Langlands.glSupercuspidalEmbedding`, not the proposition that states it.
Its implemented proof composes the following independent lower results:

- `CuspidalSupport.cuspidalEmbedding` obtains an irreducible quasicuspidal
  Levi quotient of a nonzero normalized Jacquet module and embeds the source
  by backward Frobenius reciprocity. The nonzero Jacquet module is chosen
  by maximal block count; a surjection from the refined Jacquet module
  proves quasicuspidality. Admissibility comes from the direct Cartan,
  compact averaging and countable-dimensional Schur argument, followed by
  admissibility of normalized induction and its subrepresentations.
- `CuspidalSupport.padicLeviCuspidalFactorization` iterates admissible
  irreducible two-factor tensor factorization, reflects quasicuspidality
  to each tensor factor through coinvariants, and realizes each factor
  in the prescribed universe using a countable spanning orbit and basis.
  The two-factor proof uses compact averaging, minimal dimension of fixed
  spaces, admissible Schur and Jacobson density.
- `T.exists_cuspidalSubrepresentation_of_levi_equiv` induces the actual Levi
  equivalence and composes it with the actual injection. It uses the same
  upper parabolic and positive half-modulus convention as the target.

A private Lean-service audit traversed the imported kernel types and values
of this theorem's transitive project constants, including private helpers,
opaque values and inductive constructors. It reached 1,085 project constants
in 105 project modules. Mathlib and Lean constants terminate traversal since
those upstream modules cannot depend on project declarations. The reached
classification constants consist only of the supercuspidal definitions,
cuspidality under equivalence and conjugation, cuspidal-product packaging,
and the actual irreducible-subrepresentation relation. No excluded
classification or exhaustion theorem occurs. The separate import closure
has 167 project modules and also contains none of the excluded proof modules.
The development declaration inspection reports only `propext`,
`Classical.choice` and `Quot.sound` as axioms.

The singleton bridge's declaration-level audit is documented in its paired
Markdown. It uses actual one-block evaluation, trivial determinant twist,
rank transport and algebraic Schur. The rank-zero result uses only the empty
normalized product's scalar-line equivalence and trivial-group
irreducibility. Although the rank-zero module imports
`OrderedMultisegmentHeadReduction`, only its elementary scalar-line and
empty-product equivalences enter that result; no special-head existence or
classification conclusion enters the proof.

Consequently this auxiliary uses no segment analytic classification,
multisegment special-head exhaustion, ordered special-head existence,
quotient coverage, tempered block uniqueness, square-integrable Langlands
classification, square-integrable exhaustion, regular exhaustion, or any
transitive proof dependency on their conclusions. It is derived by internal
composition of the stated published lower results and the singleton bridge.
It proves nonemptiness only and does not complete the parent exhaustion task.
