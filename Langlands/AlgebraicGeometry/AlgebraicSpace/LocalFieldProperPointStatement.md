# Proper maps of algebraic spaces over local fields are proper on rational points

Author: Worker 105.

`LocalFieldProperPointMapStatement` states Corollary 5.6 of Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed p.16. The
registered source is `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. The module only
states the corollary and contains no proof.

Conrad writes: "Corollary 5.6. Let `f : X → Y` be a proper map between (quasi-separated)
algebraic spaces locally of finite type over a local field `k` (possibly archimedean).
The map `X(k) → Y(k)` is topologically proper."

## Objects

Throughout, `K : Type u` is a nontrivially normed field that is a locally compact
space for the topology of its norm. The algebraic spaces are the Library's actual
algebraic spaces `X Y : AlgebraicSpace (Spec (CommRingCat.of K))` from
`Langlands/AlgebraicGeometry/AlgebraicSpace/Basic.lean`, and `f : X ⟶ Y` is a morphism
of algebraic spaces over `Spec K`. The statement uses only published definitions and
Mathlib.

- `IsQuasiSeparated X` (from `RingPoints.lean`) says that the diagonal of `X` is
  representable and that every represented projection of it is a quasi-compact
  morphism of schemes.
- `LocallyOfFiniteTypeOverBase X` (from `StructuralAtlasGeometry.lean`) says that `X`
  has an étale surjective atlas by an actual scheme that is locally of finite type over
  `Spec K`.
- `IsProperMorphism f` (from `SpaceMorphismProperties.lean`) says that `f` is
  separated, quasi-compact, locally of finite type and universally closed, in the
  sense of the Stacks Project, *Morphisms of Algebraic Spaces*, Definition 40.1
  (Tag 03ZM). The morphism `f` need not be representable. Each of the four conditions
  is explained in `SpaceMorphismProperties.md`.
- `RingPoints K X K` (from `RingPoints.lean`) is the set `X(K)` of rational points, and
  `RingPoints.map f : X(K) → Y(K)` is the map induced by `f`.
- `etaleChartTopology K X` (from `EtaleChartTopology.lean`) is the strongest topology
  on `X(K)` making every map `U(K) → X(K)` continuous, for étale maps `U → X` from
  actual schemes of finite type over `K`, where `U(K)` has the scheme point topology.
  This is the topology that Conrad constructs in the proof of Proposition 5.4.
- `IsProperMap` is Mathlib's proper map: a continuous map `g` such that, for every
  filter `ℱ` on the source, every cluster point of the image filter `g ℱ` is the image
  of a cluster point of `ℱ`. Mathlib proves that this is equivalent to being
  continuous and closed with compact fibres
  (`isProperMap_iff_isClosedMap_and_compact_fibers`), and that preimages of compact
  sets are compact (`IsProperMap.isCompact_preimage`).

## The statement

`LocalFieldProperPointMapStatement` says: for every nontrivially normed field
`K : Type u` with `LocallyCompactSpace K`, and every morphism `f : X ⟶ Y` of algebraic
spaces over `Spec K` with `IsQuasiSeparated X`, `LocallyOfFiniteTypeOverBase X`,
`IsQuasiSeparated Y`, `LocallyOfFiniteTypeOverBase Y` and `IsProperMorphism f`, the map
`RingPoints.map f : X(K) → Y(K)` is an `IsProperMap` when `X(K)` carries
`etaleChartTopology K X` and `Y(K)` carries `etaleChartTopology K Y`.

## Relation to the source and derived content

A local field is a field with a locally compact, non-discrete field topology: `ℝ`,
`ℂ`, a finite extension of `ℚ_p` or a field of Laurent series over a finite field.
Each of these has an absolute value inducing its topology, and conversely a
nontrivially normed field that is locally compact is non-discrete. So the hypotheses
on `K` describe exactly the local fields, with archimedean ones included as Conrad
says. Local fields are complete, hence henselian valued fields in Conrad's sense
(printed p.14), so they are covered by his Proposition 5.4.

Conrad's "topologically proper" is formalized as Mathlib's `IsProperMap`, the
Bourbaki notion. It implies that preimages of compact sets are compact. When `Y(K)` is
Hausdorff and locally compact, Mathlib's `isProperMap_iff_isCompact_preimage` shows
that the two readings agree for continuous maps. For a quasi-separated `Y` the space
`Y(K)` need not be Hausdorff (Conrad's Example 5.5, printed p.16), and then the
Bourbaki form is the stronger reading. Conrad's first reduction (printed p.16), "It
suffices to prove properness of `X(k) ×_{Y(k)} Y′(k) → Y′(k)`", is valid for the
Bourbaki notion: closedness of a map and of its products with identity maps descends
along the surjective open map `Y′(k) → Y(k)`.

Conrad's parenthetical "(quasi-separated)" refers to his standing convention for
Section 5 (printed p.13) that algebraic spaces are quasi-separated. Both `X` and `Y`
are assumed quasi-separated and locally of finite type over `K`, as in the source.

Conrad's topologies on `X(k)` and `Y(k)` are those of his Proposition 5.4. The
statement uses the étale-chart topology instead, as the published statements of
Corollary 5.12 and Proposition 5.11 do. Conrad's existence proof of Proposition 5.4
(printed p.15) asserts that this topology "does the job". That claim is stated
separately as `EtaleChartTopologyAdmissibleStatement`; with it and the uniqueness part
of Proposition 5.4, the étale-chart topology is the topology of Proposition 5.4 on
quasi-separated spaces locally of finite type. Using the concrete topology keeps the
statement about the actual point spaces.

Also derived here: the name of the statement and the description of local fields as
locally compact nontrivially normed fields.

## Not stated here

Conrad's proof reduces by an étale scheme cover `Y′ → Y` with `Y′(k) → Y(k)`
surjective to the case that `Y` is a scheme, and then uses Chow's lemma for algebraic
spaces [Kn, IV, 3.1] and the method of proof of Proposition 4.4. These steps are proof
material.
