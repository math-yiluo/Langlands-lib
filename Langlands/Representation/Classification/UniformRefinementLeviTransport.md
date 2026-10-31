# Uniform refinement Levi transport

Author: Worker 167.

This internal supporting unit identifies actual inverse permutation conjugation
on a surviving uniform refinement with the nested product-Levi reindexing,
then constructs the corresponding actual representation equivalence. It retains
the source-intersection equality, divisibility of every source piece, and the
minimality of the original coarse permutation as hypotheses. All declarations
are in `Langlands.Classification.ShuffleRefinement`.

## Actual Levi coordinates

Fix an arbitrary field `K`, natural numbers `m,r`, `hr : 0 < r`, a source
shape `B : BlockShape (m * r)`, a permutation `w` of the ambient coordinates,
and `S : BlockRefinement B`. Write `C = BlockShape.uniform m r hr`. Assume

```text
hS : sourceLevi K B C w = refinedLevi K B S,
hw : IsMinimalRepresentative B C w,
hdiv : ∀ j i, r ∣ (S j).size i.
```

The existing realization gives actual conjugacy of `B.flatten S` with `C`
and the equivalence `e = refinementBlockEquiv hr B w S hS hdiv` from nested
source-piece labels to target blocks. Write
`hs ⟨j,i⟩ = source_size_eq_of_dvd hr B w S hS j i (hdiv j i)`;
it identifies the rank of that source piece with `r`.

`flattenedLeviProductEquiv_leviConjugation_symm` proves, for every `z : C.Levi K`,

```text
flattenedLeviProductEquiv K B S
  ((leviConjugation (B.flatten S) C w
    (conjugatesLevi_flatten_uniform hr B w S hS hdiv)).symm z)
  = C.nestedLeviEquiv B S e hs K z.
```

Both sides are actual nested tuples of matrices. The proof tests the two
entries of each nested factor, embeds that factor into the ambient matrix
using `flattenedLeviEquiv_embedding`, and applies the actual inverse
conjugation embedding identity. The permutation matrix entry formulas replace
the source coordinates by their images under `w`. Applying
`source_piece_coordinates` twice and extracting the target diagonal block
produces exactly the matrix entries with `Fin.cast hs` in both coordinates.
No minimality theorem about flattened shapes is required.

## Actual tensor equivalence

Now fix `{p : ℕ} [Fact p.Prime]`, `F : PadicField.{uF} p`, its compatible
topological data `T`, and the same hypotheses over `F.Carrier`. For arbitrary
smooth factors `σ t : SmoothRep.{0,uF,uV} ℂ (GeneralLinear r F.Carrier)`, let

```text
τ j i := (hs ⟨j,i⟩).symm ▸ σ (e ⟨j,i⟩),
ρ := FiniteTensor.external (fun j =>
       FiniteTensor.external (fun i => (τ j i).representation)).
```

`uniformRefinementTensorEquiv F T hr B w S hS hw hdiv σ` constructs an actual
`Representation.Equiv` from `FiniteTensor.external (fun t => (σ t).representation)`
to

```text
transport (B.flatten S) C w
  (conjugatesLevi_flatten_uniform hr B w S hS hdiv)
  (ρ.comp (flattenedLeviProductEquiv F.Carrier B S).toMonoidHom).
```

Thus both actions are actions of the actual target product Levi `C.Levi`.
The target first pulls the nested tensor to the flattened source product and
then uses the existing inverse Weyl-conjugation convention for `transport`.
Every rank cast in `τ` is retained. The underlying linear equivalence is the
published `FiniteTensor.glRefinementEquiv` for exactly `C,B,S,e,hs,σ`.
Its intertwining identity is evaluated at
`C.leviRefinementEquiv B S e hs F.Carrier z`; the inverse source map cancels.
The inverse `refinedLeviEquiv` cancels on the other side, leaving
`C.nestedLeviEquiv`. The preceding group identity then gives the required
transported action. This proves intertwining on the whole tensor carrier.

The field universe and carrier universe remain independent. There are no
irreducibility, admissibility, dimension, unitarity, or extra representation
equivalence hypotheses. There is no additional positivity assumption on `m`;
rank zero includes the empty overall shapes and empty external tensor.

## Provenance, reuse and dependency audit

The provenance is internal finite-coordinate, matrix and representation algebra.
No original literature theorem is newly asserted. Principal proved inputs are:

| Input | Origin and role | Independence |
| --- | --- | --- |
| `source_size_eq_of_dvd`, `source_piece_coordinates`, `refinementBlockEquiv`, `conjugatesLevi_flatten_uniform` | The finite supporting units `UniformRefinementCombinatorics`, `UniformRefinementCoordinates`, and `UniformRefinementShuffleRealization` of task `0c90f7e4-78fa-43fd-8736-238bb3e8617d`; actual sizes, coordinates, labels and subgroup conjugacy. | Derived from explicit intersection equality, divisibility and coordinate order; no Jacquet formula is assumed. |
| `flattenedLeviProductEquiv`, `flattenedLeviEquiv_embedding` | Published `Geometric.FlattenedLevi`; actual nested and flattened matrix coordinates. | Product reindexing and entrywise block-diagonal matrix algebra. Its flattening input is `CuspidalSupport.MinimalJacquetProof`, task `f28607f5-1eef-4329-ae18-2576ef25ab6a`; its minimal-Jacquet theorem is unused. |
| `leviConjugation_symm_embedding`, `transport` | Published `CuspidalSupport.LeviDefinitions`; actual inverse permutation conjugation and representation pullback. | Defined from actual block embeddings and an explicit conjugacy proof; inverse group identities prove the embedding formula. |
| `leviEmbedding_apply_same`, permutation entry formulas | Published `Group.GL.Blocks` and `Group.GL.Maps`. | Direct matrix-coordinate algebra. |
| `nestedLeviEquiv`, `leviRefinementEquiv` | Published `Group.GL.RefinementCoordinates`. | Product reindexing by a label bijection and exact matrix-size equalities. No ambient comparison theorem is needed here. |
| `FiniteTensor.glRefinementEquiv` | Published `Tensor.GLRefinement`, with `Tensor.FiniteRegrouping` and `Tensor.FiniteEquivalences`. | Equality-induced carrier transport and tensor regrouping; intertwining is proved from tensor extensionality and the exact inverse group-coordinate formula. No grouping or classification theorem is assumed. |

The complete recursive project import closure has 103 modules. Compared with
`UniformRefinementShuffleRealization`, the only five added imports are
`Group.GL.RefinementCoordinates`, `Geometric.FlattenedLevi`,
`Tensor.FiniteEquivalences`, `Tensor.FiniteRegrouping`, and `Tensor.GLRefinement`.
Their lower imports already occur in the realization closure. All are the
unchanged published coordinate or tensor constructions described above.
The classification closure consists of the five finite supporting units,
`ConstituentRelations`, `CuspidalJacquetMultiplicityStatement`, `Essential`,
`LanglandsData`, `SegmentEdgeCombinatorics`, `Segments`, `Supercuspidal`,
`SupercuspidalTwist`, `Tempered`, and `TwoSegmentSocleShuffleJacquetStatement`.
The last module supplies definitions, not a proved shuffle Jacquet formula.
The remaining imports supply lower matrix, refinement, induction, coinvariant,
twist, tensor, representation and filtration-definition infrastructure.

The recursive closure contains none of the parent's excluded reverse-product
structure, reducibility, socle or special-head product criterion, adjacent or
two-segment commutation, linked gluing, ordered multisegment existence,
exhaustion, square-integrable classification, quotient-Hom or derivative
inputs. The independently reviewed `UniformRefinementShuffleRealization` pair
must be published before this unit is integrated; its hypotheses remain
explicit here.

`Tensor.FlattenedGLRefinement` already handles literal flattening with its
canonical block correspondence. This unit supplies the distinct map induced
by the realized permutation into a uniform target, reusing the same general
rank-aware tensor equivalence rather than duplicating its construction.

No geometric-lemma filtration, vanishing assertion, segment Jacquet formula,
shuffle Jacquet formula, or parent `JuxtaposedSegmentSocleReverseProductStructure`
is proved by this supporting unit.
