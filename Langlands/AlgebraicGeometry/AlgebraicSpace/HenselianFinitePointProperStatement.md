# Finite maps of algebraic spaces are proper on rational points

Author: Worker 105.

`HenselianFinitePointProperStatement` states Corollary 5.12 of Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed p.20.
`HenselianCharZeroAlgebraicallyClosedInCompletionStatement` states the
characteristic-zero part of the remark that follows it. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. The module only
states these results and contains no proofs.

Conrad's Corollary 5.12 (printed p.20) reads: "Let `f : X → Y` be a finite map between
separated algebraic spaces locally of finite type over a henselian valued field `k`. If
`k` is algebraically closed in `k̂` then `X(k) → Y(k)` is topologically proper." The
next sentence reads: "The hypothesis that `k` is algebraically closed in `k̂` holds if
`char(k) = 0` or `k` is non-archimedean with an excellent valuation ring."

## Objects

Throughout, `K : Type u` is a nontrivially normed field. The algebraic spaces are the
Library's actual algebraic spaces `X Y : AlgebraicSpace (Spec (CommRingCat.of K))` from
`Langlands/AlgebraicGeometry/AlgebraicSpace/Basic.lean`, and `f : X ⟶ Y` is a morphism
of algebraic spaces over `Spec K`. The statements use only published definitions and
Mathlib.

- `IsHenselianValuedField K` (from
  `Langlands/AlgebraicGeometry/PointTopology/HenselianEtalePointStatement.lean`) says
  that the norm of `K` extends uniquely to an absolute value on every algebraic
  extension field. This is Conrad's definition of a henselian valued field (printed
  p.14).
- `UniformSpace.Completion K` is Mathlib's completion `K̂` of `K` for the uniform
  structure of its norm. Mathlib makes it a field and a `K`-algebra whose structure map
  is the canonical inclusion `K → K̂`. `algebraicClosure K K̂` is Mathlib's
  intermediate field of the elements of `K̂` that are algebraic over `K`. The equation
  `algebraicClosure K (UniformSpace.Completion K) = ⊥` says that every element of `K̂`
  algebraic over `K` lies in `K`, that is, `K` is algebraically closed in `K̂`.
- `IsSeparated X` (from `RingPoints.lean`) says that the diagonal of `X` is a
  representable closed immersion: it is Conrad's separatedness. Separated spaces are
  quasi-separated, so Conrad's standing convention for Section 5 (printed p.13) holds.
- `LocallyOfFiniteTypeOverBase X` (from `StructuralAtlasGeometry.lean`) says that `X`
  has an étale surjective atlas by an actual scheme that is locally of finite type over
  `Spec K`.
- `IsFinite (hom f)` (from `SchemeLocalGeometry.lean`) says that `f`, viewed as a
  morphism of presheaves, is representable by actual schemes and that every
  represented projection is a finite morphism of schemes in Mathlib's sense (affine,
  with finite ring maps on affine opens). This is the Stacks Project's notion of a
  finite morphism of algebraic spaces (Morphisms of Algebraic Spaces, Section 67.45,
  Tag 03ZN), as explained in `SchemeLocalGeometry.md`.
- `RingPoints K X K` (from `RingPoints.lean`) is the set `X(K)` of rational points, and
  `RingPoints.map f : X(K) → Y(K)` is the map induced by `f`.
- `etaleChartTopology K X` (from `EtaleChartTopology.lean`) is the strongest topology
  on `X(K)` making every map `U(K) → X(K)` continuous, for étale maps `U → X` from
  actual schemes of finite type over `K`, where `U(K)` has the scheme point topology.
  This is the topology that Conrad constructs in the proof of Proposition 5.4.
- `IsProperMap` is Mathlib's proper map: a continuous map `g` such that, for every
  filter `ℱ` on the source, every cluster point of the image filter `g ℱ` is the image
  of a cluster point of `ℱ`. Mathlib proves that
  this is equivalent to being continuous and closed with compact fibres
  (`isProperMap_iff_isClosedMap_and_compact_fibers`), and that preimages of compact
  sets are compact (`IsProperMap.isCompact_preimage`).

## The statements

`HenselianFinitePointProperStatement` says: for every nontrivially normed field
`K : Type u` with `IsHenselianValuedField K` and
`algebraicClosure K (UniformSpace.Completion K) = ⊥`, and every morphism
`f : X ⟶ Y` of algebraic spaces over `Spec K` with `IsSeparated X`,
`LocallyOfFiniteTypeOverBase X`, `IsSeparated Y`, `LocallyOfFiniteTypeOverBase Y` and
`IsFinite (hom f)`, the map `RingPoints.map f : X(K) → Y(K)` is an `IsProperMap` when
`X(K)` carries `etaleChartTopology K X` and `Y(K)` carries `etaleChartTopology K Y`.

`HenselianCharZeroAlgebraicallyClosedInCompletionStatement` says: every nontrivially
normed field `K : Type u` with `IsHenselianValuedField K` and `CharZero K` satisfies
`algebraicClosure K (UniformSpace.Completion K) = ⊥`.

## Relation to the source and derived content

Conrad's "topologically proper" is formalized as Mathlib's `IsProperMap`, the Bourbaki
notion. Conrad's proof (printed p.20) ends: "Since a topologically closed map between
Hausdorff spaces is proper when its fibers are finite, it suffices to prove closedness
of the map on `k`-points." The notion of properness in this sentence is the Bourbaki
notion: a continuous closed map with compact fibres. It implies that preimages of
compact sets are compact, so the statement also gives the weaker reading of
"proper".

Conrad's topologies on `X(k)` and `Y(k)` are those of his Proposition 5.4. The
statement uses the étale-chart topology instead, as the published statements of
Proposition 5.11 do. Conrad's existence proof of Proposition 5.4 (printed p.15) asserts
that this topology "does the job". That claim is stated separately as
`EtaleChartTopologyAdmissibleStatement`; with it and the uniqueness part of
Proposition 5.4, the étale-chart topology is the topology of Proposition 5.4 on
quasi-separated spaces locally of finite type. Using the concrete topology keeps the
statement about the actual point spaces.

The characteristic-zero statement is the first case of Conrad's remark, for both
archimedean and non-archimedean `K`. Conrad gives no argument for it. It is a
consequence of the published `HenselianSeparablyClosedInCompletionStatement` (a
henselian valued field is separably closed in its completion, proved in
`HenselianEtalePointProof.lean`), because in characteristic zero every algebraic
element is separable. Also derived here: the names of the two statements.

## Not stated here

- The second case of Conrad's remark, for non-archimedean `K` with an excellent
  valuation ring, is not stated: neither Mathlib nor the Library defines excellent
  rings.
- Conrad's proof first reduces to complete `k`: the square formed by `X(k) → X(k̂)`
  and `Y(k) → Y(k̂)` is topologically cartesian, using Proposition 5.11(2) (published
  as `HenselianCompletionPointEmbeddingStatement`) and the hypothesis that `k` is
  algebraically closed in `k̂`. It then works étale-locally on `Y`, reduces to
  `X = Spec(A[t]/(h))` for a monic `h` over an affine `Y = Spec(A)`, and cites the
  continuity of roots [BGR, 3.4.1/2] for closedness. These steps are proof material.
