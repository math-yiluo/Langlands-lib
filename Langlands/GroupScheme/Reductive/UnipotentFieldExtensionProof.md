# Preservation of unipotence under field extension: proof

Authors: Worker 1395 and Worker 16. Worker 1395 supplied the proof draft and its coordinate-algebra route; Worker 16 checked the exact target, source correspondence and final submission.

The theorem `Langlands.GroupScheme.unipotentFieldExtensionStatement.{u}` has type exactly
`Langlands.GroupScheme.UnipotentFieldExtensionStatement.{u}`. That statement is imported unchanged
from [`UnipotentFieldExtensionStatement`](UnipotentFieldExtensionStatement.md). Take fields
`k K : Type u` with `Algebra k K` and a group scheme `G` over `Spec (CommRingCat.of k)` such that
`G.X.hom` is affine and locally of finite type. If `IsUnipotent G` holds, then `IsUnipotent` holds
for the base change of `G` along `Spec.map (CommRingCat.ofHom (algebraMap k K))`. This is the
forward direction of Milne, *Algebraic Groups* (2017), Corollary 14.9, printed p.282 (one-based PDF p.298), registered as `milne-2017-algebraic-groups`, SHA-256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. The complete official errata snapshot `milne-2017-algebraic-groups-errata-2026-11-02` was read; it does not change this corollary. The printed proof refers to 14.9 for coconnectedness; the criterion is Theorem 14.5.

The proof introduces the hypotheses and applies `IsUnipotent.baseChange` from
[`Unipotent.BaseChange`](../Unipotent/BaseChange.md). That theorem needs only
`[IsAffineHom G.X.hom]`, so the `LocallyOfFiniteType` hypothesis is introduced but not used. The
proof adds no hypothesis on `k`, `K` or `G`. In particular, it permits inseparable and transcendental extensions. The conclusion uses the published `IsUnipotent` over `K`, hence tests every nonzero finite-dimensional matrix representation over `K`, including those that do not descend to `k`, with fixedness on every test scheme. It uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Route

Milne proves the corollary with his criterion that a group is unipotent exactly when its
coordinate Hopf algebra is coconnected (Theorem 14.5). The Lean proof follows the same overall
plan, passing to the coordinate Hopf algebra, extending scalars there, and coming back. It
replaces coconnectedness by an internal fixed-vector predicate on coordinate bialgebras, so it
needs no coradical theory.

1. [`Unipotent.HopfFixed`](../Unipotent/HopfFixed.md) defines `OneMemStable K B` for a
   `K`-bialgebra `B`: every nonzero finite-dimensional subspace of `B` that is stable under all
   right translations contains `1`. It also proves `exists_invariant`, a fixed-vector lemma for
   modules mapping jointly injectively into `B`.
2. [`Unipotent.CoordinateBialgebra`](../Unipotent/CoordinateBialgebra.md) proves that a
   corepresented group scheme over a field is unipotent exactly when its coordinate bialgebra
   satisfies `OneMemStable`.
3. [`Unipotent.ScalarExtension`](../Unipotent/ScalarExtension.md) proves that `OneMemStable k B`
   implies `OneMemStable K (K ⊗[k] B)` for any field extension `K` of `k`.
4. [`Unipotent.BaseChange`](../Unipotent/BaseChange.md) assembles these. The scheme `G.X.left`
   is affine. `G` is unipotent, so its coordinate Hopf algebra satisfies `OneMemStable` (step 2).
   So does the scalar extension of that Hopf algebra (step 3). Hence the spectrum of the extended
   Hopf algebra is unipotent (step 2 again). The Library's `AffineCoordinates.hopfSpecIso`, carried
   through `GroupScheme.baseChange`, together with `HopfCoordinates.baseChangeSpecIso`, identifies
   this spectrum with the base change of `G`. `IsUnipotent.of_iso` then transfers unipotence.

Each linked page describes its module's proof in detail.
