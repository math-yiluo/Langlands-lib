# Reductive groups isomorphic over the algebraic closure are isomorphic over a finite separable extension

`Langlands.GroupScheme.ReductiveGeometricIsoSeparableStatement.{u}` is a
proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be a field and let
`G G' : GroupScheme (Spec (CommRingCat.of k))` satisfy
`IsConnectedReductive G` and `IsConnectedReductive G'`. Suppose that the base
changes `(GroupScheme.baseChange (toAlgebraicClosure k)).obj G` and
`(GroupScheme.baseChange (toAlgebraicClosure k)).obj G'` are isomorphic
group schemes over `Spec (AlgebraicClosure k)`. Then there are a field
`L : Type u` and a `k`-algebra structure on `L` such that
`FiniteDimensional k L`, `Algebra.IsSeparable k L`, and the base changes of
`G` and `G'` along `Spec.map (CommRingCat.ofHom (algebraMap k L))` are
isomorphic group schemes over `Spec L`.

The ingredients are existing declarations, used without change.

- `IsConnectedReductive G` and `toAlgebraicClosure k` are from
  [`Reductive.Basic`](Basic.md). `IsConnectedReductive G` says that `G` is
  smooth, affine and connected over `k`, and that the unipotent radical of
  its base change to `AlgebraicClosure k` is trivial. That module records it
  as Milne 6.46 (p.135). `toAlgebraicClosure k` is `Spec` of the algebra
  map `k → AlgebraicClosure k`.
- `GroupScheme.baseChange` (from
  [`AbelianScheme.GroupScheme`](../../AbelianScheme/GroupScheme.md)) is base
  change of group schemes along a morphism of base schemes.
- `FiniteDimensional`, `Algebra.IsSeparable`, `AlgebraicClosure` and `Spec`
  are from Mathlib.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Corollary 23.28, p.493: "Let G and G′ be reductive groups over k. If G and
  G′ become isomorphic over k^a, then they become isomorphic over a finite
  separable extension of k."
- Its proof: "They split over a finite separable extension of k, and so the
  statement follows from the last corollary."
- The last corollary is Corollary 23.27, p.493: "Let (G, T) and (G′, T′) be
  split reductive groups over k. If G and G′ become isomorphic over k^a, then
  (G, T) and (G′, T′) are isomorphic over k."

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) has Corollaries 23.27 and
23.28 on printed p.494. The statements are the same; the proof of 23.27 is
reworded, and the proof of 23.28 is the same.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. Neither has an entry for 6.46, 23.27 or 23.28, or for
pp.135 or 352. The 2017 errata have no entry for p.493; their p.494 entry
concerns Corollary 23.32. The 2022 errata have no entry for p.494.

## Derivation from the source

- **Reductive groups.** Milne's reductive groups over `k` are
  `IsConnectedReductive`, which includes affineness. This matches the book's
  convention, recalled at the opening of Chapter 17, p.352: "Recall also
  that all algebraic groups are affine over a base field k" (2022 reprint
  p.352, same words).
- **Isomorphic over `k^a`.** `k^a` is Mathlib's `AlgebraicClosure k`, and
  `G_{k^a}` is `(GroupScheme.baseChange (toAlgebraicClosure k)).obj G`.
  "G and G′ become isomorphic over `k^a`" is the existence of an isomorphism
  of group schemes over `Spec (AlgebraicClosure k)` between these base
  changes, written `Nonempty (… ≅ …)`.
- **Finite separable extension.** "A finite separable extension of `k`" is a
  field `L` with a `k`-algebra structure, `FiniteDimensional k L` and
  `Algebra.IsSeparable k L`. The field `L` lies in the universe `u` of `k`.
  This is no restriction, because a finite extension of `k` has an
  isomorphic copy in that universe.
- **Isomorphic over `L`.** The conclusion is the existence of an isomorphism
  of group schemes over `Spec L` between the base changes of `G` and `G'`
  along `Spec.map (CommRingCat.ofHom (algebraMap k L))`.
- **Universes.** One universe `u` is used for the fields and the schemes.
  This is a formalization convention.

## Related Library results

- `Langlands.GroupScheme.LocalSplitReductiveGeometricIsoStatement` (from
  [`Reductive.LocalSplitGeometricIsoStatement`](LocalSplitGeometricIsoStatement.md))
  states a form of 23.27 over local rings: reductive groups with split
  maximal tori are isomorphic once their base changes to an algebraically
  closed field are.
- `Langlands.GroupScheme.exists_finiteGalois_hasSplitMaximalTorus` (from
  [`Torus.FiniteGaloisSplitMaximal`](../Torus/FiniteGaloisSplitMaximal.md))
  proves that a smooth affine group over a field acquires a split maximal
  torus over a finite Galois extension. It assumes the propositions
  `TorusFiniteGaloisSplittingStatement` and
  `MaximalTorusBaseChangeStatement` as explicit hypotheses.
