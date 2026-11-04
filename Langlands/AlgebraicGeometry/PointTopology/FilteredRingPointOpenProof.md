# Open stages of the actual point colimit (proof)

This module proves the published proposition `FilteredRingPointOpenStages`
from `FilteredRingPointOpenStatement`. The theorem
`filteredRingPointOpenStages` has exactly the type
`FilteredRingPointOpenStages.{u}`, so it covers every commutative ring `R`,
small filtered category `J`, diagram `F` of commutative `R`-algebras, scheme
`X` over `Spec R` and family `τ` of stage topologies, all in one arbitrary
universe `u`. It uses the actual carriers, transition maps
`p ↦ p.changeRing (F.map f).hom`, type colimit, final topology and
quotient-topologized stage images of `FilteredRingPoints` and
`FilteredRingPointTopology`. It adds no hypothesis to the statement.

## Source context

The statement isolates the topological direct-limit assertion in Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (31 December 2011),
printed page 9, section 4, first two paragraphs. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Conrad works with directed systems. The statement's extension to small
filtered categories is derived, as explained in the statement's Markdown. The
proof below is the implemented Lean route, not a transcription of Conrad's
text.

## Declarations

All helper lemmas are `private`. The section variables are `R`, `J`, `F`, `X`
and `τ` as above.

- `stage_preimage_image`. Take stages `i`, `j` and any set `V` of stage-`i`
  points. The lemma gives the preimage at stage `j` of the colimit image of
  `V`. It equals the union, over all objects `k` and arrows `f : i ⟶ k`,
  `g : j ⟶ k`, of the preimage under the `g`-transition of the image of `V`
  under the `f`-transition. Both inclusions come from Mathlib's filtered
  type-colimit equality criterion `Functor.ιColimitType_eq_iff_of_isFiltered`,
  applied to the point functor `F ⋙ ringPointFunctor R X`. Two
  representatives `p` at `i` and `q` at `j` have the same colimit class
  exactly when `f`- and `g`-transitions to some common `k` agree on them. No
  transition is cancelled, so no injectivity is used.
- `stage_open`. Assume every transition is continuous and open. Then every
  stage map `ringPointColimitι R F X i` is open. For open `V` at `i`, the
  published criterion `ringPointColimitTopology_isOpen_iff` reduces openness
  of its colimit image to openness of its preimage at every stage `j`. By
  `stage_preimage_image` that preimage is the union above. Each `V`-image is
  open because the `f`-transition is open. Its preimage is open because the
  `g`-transition is continuous. The union is therefore open.
- `stage_image_openEmbedding`. Assume every stage map is open. Then the
  inclusion `Subtype.val` of each actual stage image, carrying
  `ringPointColimitStageImageTopology`, is an open embedding into the
  colimit. The lemma does not use filteredness, which it omits with
  `omit [IsFiltered J]`. The published
  `ringPointColimitStageProjection_isQuotientMap` makes the projection from
  the stage a quotient map. The inclusion composed with the projection is the
  stage map, which is continuous by `ringPointColimitTopology_continuous_ι`.
  So the inclusion is continuous by `IsQuotientMap.continuous_iff`. It is
  injective by `Subtype.val_injective`. For openness, take an open `V` in the
  image. Its preimage under the projection is open, and the stage map sends
  that preimage onto an open set. Because the projection is surjective
  (`Set.image_preimage_eq`), this open set is the inclusion image of `V`.
  Mathlib's `IsOpenEmbedding.of_continuous_injective_isOpenMap` then gives
  the open embedding. Since the lemma uses the given quotient topology, it
  shows that this topology equals the subspace topology.
- `stage_injective`. Assume every transition is injective. Then every stage
  map is injective. When two stage-`i` points have the same colimit class,
  the same-stage criterion `Functor.ιColimitType_eq_iff_of_isFiltered'` gives
  one arrow `f : i ⟶ k` whose transition identifies them. Cancelling that
  injective transition makes them equal.
- `filteredRingPointOpenStages`. The theorem combines the three conclusions.
  `stage_open` proves the first. `stage_image_openEmbedding`, applied to the
  first, proves the second. For the third, assume injective transitions.
  Each stage map is continuous by `ringPointColimitTopology_continuous_ι`,
  injective by `stage_injective` and open by `stage_open`.
  `IsOpenEmbedding.of_continuous_injective_isOpenMap` then makes it an open
  embedding.

Only the third conclusion uses injective transitions. The first two allow
noninjective transitions, as the source does. Continuity and openness of
transitions are both used, in `stage_open`.

## Checks and scope

The development check of the theorem reports zero diagnostics and only the
axioms `propext`, `Classical.choice` and `Quot.sound`. This module supplies no
arithmetic stage topology. It does not specialize transition properties to
the global product topologies of Conrad Theorem 3.6. It proves no
algebra-colimit point comparison, varying-model comparison or model
independence result. These remain obligations of the parent development.

## Authorship

The Lean proof is Worker 105's shared draft revision 1, unchanged. This
Markdown was rewritten to describe its declarations.
