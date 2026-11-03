# Split maximal tori after a finite Galois extension

Module `Langlands.GroupScheme.Torus.FiniteGaloisSplitMaximal`. Author: Worker 1391.

This module is a helper for proof task `a41119fb-a633-4b81-a979-4b08e9ddbb15`, which proves
`SimplyConnectedCoverExistenceStatement`. That proof follows Milne, *Algebraic Groups* (2017),
Remark 23.60: build the cover over a field where the group is split, then descend it to `k`. For
that route, every semisimple group must acquire a split maximal torus over some finite Galois
extension.

The module defines one predicate, `HasSplitMaximalTorus`, and proves two theorems. The theorems
state and prove nothing new about tori. They combine these published statements:

- `MaximalTorusExistenceStatement` (module `Torus.ExistenceStatement`), proved in the Library as
  `maximalTorusExistence` (module `Torus.ExistenceProof`): every smooth affine group over a field
  has a maximal torus over that field (Milne, Corollary 17.83).
- `TorusFiniteGaloisSplittingStatement` (module `Torus.FiniteGaloisSplittingStatement`; Milne 12.18,
  12.19): every torus splits over a finite Galois extension. Here it is an explicit hypothesis
  `hsplit`.
- `MaximalTorusBaseChangeStatement` (module `Torus.MaximalBaseChangeStatement`; Milne, Theorem
  17.82): a closed torus is maximal exactly when its base change to a field extension is maximal.
  Here it is an explicit hypothesis `hbase`.

The second theorem also uses `IsSemisimpleFieldExtensionStatement` (module
`SimplyConnected.FieldExtensionStatement`: semisimplicity survives base change along a field
extension), again as an explicit hypothesis `hss`.

## `HasSplitMaximalTorus`

Let `G` be a group scheme over `Spec k` for a field `k : Type u`. `HasSplitMaximalTorus G` holds
when there are a commutative group scheme `T` over `Spec k` and a homomorphism `i : T ⟶ G` with
`IsSplitTorus T` and `IsMaximalTorus i`. So some maximal torus of `G` is split.

Source: Milne, *Algebraic Groups* (2017), Definition 19.22, printed p. 402 (PDF p. 418): "A
reductive group is splittable if it contains a split maximal torus." Chapter 21, §a, printed
p. 424 (PDF p. 440), repeats this as "G is split if some maximal torus T is split". The Lean
predicate is this condition, with "maximal torus" read as the Library's `IsMaximalTorus`. It is
defined for every group scheme over `k`, but it carries Milne's meaning only for reductive `G`.

For a general group variety, Milne's Definition 17.101 (printed p. 384, PDF p. 400) uses a
different notion: a split Borel subgroup. This module does not formalize that definition. Milne's
Proposition 21.64 (printed p. 443, PDF p. 459) states that a reductive group is splittable exactly
when it is split in the sense of 17.101. Nothing in this module uses that equivalence.

The Library had no predicate for split groups before this module. The split-group statements of
task `157eb578-930f-46eb-b229-06b87342bae8` write the same condition out as an explicit
existential.

## `exists_finiteGalois_hasSplitMaximalTorus`

Let `G` be a group scheme over `Spec k` for a field `k : Type u`, with smooth and affine structure
morphism. Assume `hsplit` and `hbase`. Then there are a field `K : Type u` and an algebra `k → K`
with these properties:

- `K` is finite-dimensional and Galois over `k`.
- `HasSplitMaximalTorus G_K` holds. Here `G_K` is the base change of `G` along
  `Spec.map (CommRingCat.ofHom (algebraMap k K))`.

Proof. `maximalTorusExistence` gives a maximal torus `i₀ : T₀ ⟶ G` over `k`. By the definition of
`IsMaximalTorus`, `T₀` is a torus and `i₀` is a closed subgroup. Applying `hsplit` to `T₀` gives a
finite Galois extension `K / k` over which the base change of `T₀` is split. The witnesses for
`HasSplitMaximalTorus G_K` are the commutative base change `T` of `T₀` and the base-changed map
`i` of `i₀`. `T` is split by the `hsplit` conclusion: the underlying group scheme of the commutative
base change is, by definition, the base change of `T₀`. `i` is maximal by the forward direction of
`hbase` applied to `i₀`.

## `exists_finiteGalois_hasSplitMaximalTorus_of_isSemisimple`

Let `G` be a semisimple group over `Spec k` (`IsSemisimple G`). Assume `hsplit`, `hbase` and `hss`.
Then the first theorem's conclusion holds, and in addition `G_K` is semisimple. This matches the
hypotheses of `SplitSimplyConnectedCoverExistenceStatement` (statement task
`157eb578-930f-46eb-b229-06b87342bae8`) over `K`.

Proof. `IsSemisimple G` contains `IsConnectedReductive G`, which supplies the smooth and affine
structure morphism. The first theorem gives `K` and `HasSplitMaximalTorus G_K`, and
`hss k K G hG` gives that `G_K` is semisimple.
